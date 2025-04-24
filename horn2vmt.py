import sys
from pysmt.shortcuts import *
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.exceptions import UnknownSmtLibCommandError
from pysmt.logics import get_logic_by_name
import pysmt.smtlib.commands as smtcmd
from mathsat import *
import vmt
try:
    # Python 2
    import cStringIO as StringIO
    StringIOClass = StringIO.StringIO
except ImportError:
    # Python 3
    from io import StringIO
    StringIOClass = StringIO
import math
import itertools


def to_smt2(f):
    buf = StringIOClass()
    pr = SmtDagPrinter(buf)
    pr.printer(f)
    return buf.getvalue()


def warn(msg):
    sys.stderr.write('WARNING: ')
    sys.stderr.write(msg)
    sys.stderr.flush()
    

def conjunctive_partition(formula):
    to_process = [formula]
    seen = set()
    op = pysmt.operators.AND
    while to_process:
        cur = to_process[-1]
        to_process.pop()
        if cur and cur not in seen:
            seen.add(cur)
            if cur.node_type() == op:
                to_process += cur.args()
            else:
                yield cur


class CHC(object):
    def __init__(self, constr, body, head, qvars):
        self.constr = constr
        self.body = body
        self.head = head
        self.qvars = qvars

    def get_free_variables(self):
        fv = self.constr.get_free_variables() - self.qvars
        for b in self.body:
            fv -= set(list(b.args()) + [b.function_name()])
        if self.head.is_function_application():
            fv -= set(list(self.head.args()) + [self.head.function_name()])
        return fv

    def __str__(self):
        def pexpr(f): return serialize(f) if f else str(f)
        return '%s & [%s] => %s' % (pexpr(self.constr),
                                    ', '.join(str(pexpr(p)) for p in self.body),
                                    pexpr(self.head))

    __repr__ = __str__

# end of class CHC
        

class Defaults(object):
    def __init__(self):
        self.b = -1
        self.i = -1
        self.r = -1

    def get(self, tp):
        if tp.is_bool_type():
            self.b += 1
            return Symbol('.xb%d' % self.b, tp)
        elif tp.is_int_type():
            self.i += 1
            return Symbol('.xi%d' % self.i, tp)
        else:
            assert tp.is_real_type()
            self.r += 1
            return Symbol('.xr%d' % self.r, tp)

# end of class Defaults


class PredMapper(object):
    def __init__(self, msat_env, msat_converter, preds, clauses, defaults):
        self.msat_env = msat_env
        self.msat_converter = msat_converter
        self.preds = preds
        self.numpreds = len(preds)
        self.clauses = clauses
        self.defaults = defaults
        self.bigpred = None
        self.pred2pos = {}
        self.pred2sel = {}
        self.pred_selectors = []
        self.pred_args = {}


    def get_model(self):
        #print 'clauses:\n%s\n' % pprint.pformat(self.clauses)
        for cls in self.clauses:
            self.debug_check_clause(cls)
            
        self.make_binary()
        #print 'clauses:\n%s\n' % pprint.pformat(self.clauses)
        self.make_single_predicate()
        #print 'clauses:\n%s\n' % pprint.pformat(self.clauses)
        self.combine_same_arity()
        #print 'clauses:\n%s\n' % pprint.pformat(self.clauses)
        return self.build_model()
    

    def make_binary(self):
        def getkey(p1, p2):
            if p1.function_name().symbol_name() > \
                   p2.function_name().symbol_name():
                p1, p2 = p2, p1
            return (p1.function_name(), p2.function_name()), p1, p2

        cache = {}
        extra = []
        
        for cls in self.clauses:
            self.debug_check_clause(cls)
            
            while len(cls.body) > 2:
                p1, p2 = cls.body[-2:]
                cls.body.pop()
                cls.body.pop()
                key, p1, p2 = getkey(p1, p2)
                add = False
                if key not in cache:
                    sig = key[0].symbol_type().param_types + \
                          key[1].symbol_type().param_types
                    p = Symbol(".B{%s,%s}" % (key[0].function_name(),
                                              key[1].function_name()),
                               types.FunctionType(types.BOOL, sig))
                    cache[key] = p
                    add = True
                else:
                    p = cache[key]

                args = p1.args() + p2.args()
                cls.body.append(Function(p, args))

                if add:
                    constr = []
                    newargs = []
                    for i, a in enumerate(args):
                        assert a.is_symbol()
                        aa = Symbol('.y_%s' % a.symbol_name(), a.symbol_type())
                        if a.symbol_type().is_bool_type():
                            constr.append(Iff(a, aa))
                        else:
                            constr.append(Equals(a, aa))
                        newargs.append(aa)
                    extra.append(CHC(And(constr), [p1, p2],
                                     Function(p, newargs), cls.qvars))
                    self.preds.append(p)

        self.clauses += extra
                    

    def make_single_predicate(self):
        if len(self.preds) == 1:
            self.bigpred = self.preds[0]
            return

        def key(p):
            return (len(p.symbol_type().param_types), p.symbol_name())
        preds = sorted(self.preds, key=key, reverse=True)

        self.pred2pos = {}
        sig = []
        j = 0
        for p in preds:
            d = []
            self.pred2pos[p] = d
            used = set()
            for i, t in enumerate(p.symbol_type().param_types):
                found = None
                for j, tt in enumerate(sig):
                    if t == tt and j not in used:
                        found = j
                        break
                if found is None:
                    found = len(sig)
                    sig.append(t)
                d.append(found)
                used.add(found)

        n = max(1, int(math.ceil(math.log(len(preds), 2))))
        self.pred_selectors = [
            [Symbol('.p%d' % i) for i in xrange(n)],
            [Symbol('.p%d_0' % i) for i in xrange(n)],
            [Symbol('.p%d_1' % i) for i in xrange(n)]
            ]

        sig += ([types.BOOL] * n)
        self.bigpred = Symbol(".P", types.FunctionType(types.BOOL, sig))
        self.pred2sel = { p : k for (k, p) in enumerate(preds) }

        def mksel(k, j):
            l = []
            for i, b in enumerate(self.pred_selectors[j]):
                if k & (1 << i):
                    l.append(b)
                else:
                    l.append(Not(b))
            return And(l)

        for cls in self.clauses:
            self.debug_check_clause(cls)
            
            def conv(j, p):
                used = set()
                f = p.function_name()
                d = self.pred2pos[f]
                args = [None] * (len(sig) - n)
                for i, a in enumerate(p.args()):
                    args[d[i]] = a
                    if j == 0:
                        used.add(d[i])
                args += self.pred_selectors[j]
                for i, a in enumerate(args):
                    if a is None:
                        args[i] = self.defaults.get(sig[i])
                if j == 0:
                    self.pred_args[f] = used
                return Function(self.bigpred, args), mksel(self.pred2sel[f], j)
            
            for j, p in enumerate(cls.body):
                cls.body[j], c = conv(j, p)
                cls.constr = And(cls.constr, c)
            if cls.head.is_function_application():
                cls.head, c = conv(2, cls.head)
                cls.constr = And(cls.constr, c)

    def combine_same_arity(self):
        def key(cls):
            return (len(cls.body), cls.head.is_function_application())

        self.clauses.sort(key=key)
        clauses = []

        for k, g in itertools.groupby(self.clauses, key):
            g = list(g)
            while len(g) > 1:
                c1, c2 = g[-2:]
                g.pop()
                g.pop()
                subst = {}
                for i, p in enumerate(c1.body):
                    subst.update(dict(zip(p.args(), c2.body[i].args())))
                if c1.head.is_function_application():
                    subst.update(dict(zip(c1.head.args(), c2.head.args())))
                constr = Or(c1.constr.substitute(subst), c2.constr)
                g.append(CHC(constr, c2.body, c2.head, c1.qvars | c2.qvars))
            clauses.append(g[0])
            self.debug_check_clause(g[0])

        self.clauses = clauses

    def debug_check_clause(self, cls):
        if cls.get_free_variables():
            print('CLAUSE:', cls)
            print('FREE VARS:', cls.get_free_variables())
            assert False

    def build_model(self):
        pred = self.bigpred
        assert pred is not None
        
        sv = [Symbol('.x%d' % i, t)
              for i, t in enumerate(pred.symbol_type().param_types)]
        sv0 = [Symbol('.x%d_0' % i, t)
               for i, t in enumerate(pred.symbol_type().param_types)]
        sv1 = [Symbol('.x%d_1' % i, t)
               for i, t in enumerate(pred.symbol_type().param_types)]

        init = None
        trans = None
        bad = None

        for cls in self.clauses:
            if cls.head.is_function_application() and \
                   cls.head.function_name() == pred:
                if not cls.body:
                    assert init is None
                    assert not cls.get_free_variables()
                    init = cls.constr.substitute(
                        dict(zip(cls.head.args(), sv)))
                else:
                    assert 1 <= len(cls.body) <= 2
                    ## m.inputvars = list(cls.get_free_variables())
                    sm = dict(zip(cls.body[0].args(), sv))
                    sm.update(dict(zip(cls.head.args(), sv1)))
                    if len(cls.body) == 2:
                        raise Exception("non-linear clause found")
                        ## assert m.trans2 is None
                        ## sm.update(dict(zip(cls.body[1].args(), sv0)))
                        ## m.trans2 = cls.constr.substitute(sm)
                    else:
                        assert trans is None
                        trans = cls.constr.substitute(sm)                    
            else:
                assert cls.head.is_false()
                assert len(cls.body) == 1, cls
                assert not cls.get_free_variables()
                assert bad is None
                bad = cls.constr.substitute(dict(zip(cls.body[0].args(), sv)))

        def to_msat(f):
            return self.msat_converter.convert(f)

        if init is None:
            init = TRUE()
        if trans is None:
            trans = TRUE()
        if bad is None:
            bad = FALSE()

        m = vmt.VmtModel(zip(map(to_msat, sv), map(to_msat, sv1)),
                         to_msat(init), to_msat(trans),
                         [to_msat(Not(bad))])
        return m

# end of class PredMapper


def parse(src, msat_env, msat_converter):
    p = SmtLibParser()
    s = p.get_script(src)
    
    decls = list(s.filter_by_command_name(set([smtcmd.DECLARE_FUN])))
    preds = set()
    for d in decls:
        pred = d.args[0]
        if pred.symbol_type().is_bool_type() or \
               (hasattr(pred.symbol_type(), 'return_type') and
                pred.symbol_type().return_type.is_bool_type()):
            preds.add(pred)

    def split_body(body):
        p, constr = [], TRUE()
        for a in conjunctive_partition(body):
            if a.is_function_application() and a.function_name() in preds:
                p.append(a)
            else:
                constr = And(constr, a)
        return p, constr

    clauses = []
    defaults = Defaults()
    
    assertions = list(s.filter_by_command_name(set([smtcmd.ASSERT])))
    for cmd in assertions:
        f = cmd.args[0]
        if f.is_not() and f.arg(0).is_exists():
            #print 'converting: ', f.arg(0).serialize()
            # (not (exists v f)) -> (forall v (=> f false))
            f = ForAll(f.arg(0).quantifier_vars(),
                       Implies(f.arg(0).arg(0), FALSE()))
        if not f.is_quantifier():
            warn('ignoring non-quantified assertion: %s\n' % to_smt2(f))
            continue
        
        qvars = f.quantifier_vars()
        matrix = f.arg(0)
        if matrix.is_implies():
            head = matrix.arg(1)
            body = matrix.arg(0)
        else:
            head = matrix
            body = TRUE()

        body, constr = split_body(body)
        if not head.is_function_application() and not head.is_false():
            constr = And(constr, Not(head))
            head = FALSE()
        # make sure that each var occurs only once as a predicate argument
        seen = set()
        def norm(f, constr):
            p = f.function_name()
            args = []
            for i, a in enumerate(f.args()):
                if a in seen or not a.is_symbol():
                    tp = p.symbol_type().param_types[i]
                    aa = defaults.get(tp)
                    if tp.is_bool_type():
                        eq = Iff(a, aa)
                    else:
                        eq = Equals(a, aa)
                    a = aa
                    constr = And(constr, eq)
                seen.add(a)
                args.append(a)
            return Function(p, args), constr
            
        for i, f in enumerate(body):
            body[i], constr = norm(f, constr)
        if head.is_function_application():
            head, constr = norm(head, constr)
            
        clauses.append(CHC(constr, body, head, frozenset(qvars)))

    pm = PredMapper(msat_env, msat_converter, list(preds), clauses, defaults)
    return pm.get_model()


def main():
    if len(sys.argv) < 2:
        print("Usage: python horn2vmt.py <input_file>")
        return
    
    input_file = sys.argv[1]
    
    with Solver(name='msat') as s:
        with open(input_file, 'r') as f:
            model = parse(f, s.msat_env, s.converter)
            vmt.write(s.msat_env, model, sys.stdout)


if __name__ == '__main__':
    main()
