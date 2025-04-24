from mathsat import *
import vmt
import os, sys
import argparse
from functools import reduce


_verb = False
def log(fmt, *args):
    if _verb:
        sys.stdout.write(';; ')
        sys.stdout.write(fmt % tuple(args))
        sys.stdout.write('\n')
        sys.stdout.flush()


class LtlEncoder(object):
    def __init__(self, env):
        self.env = env
        tp = msat_get_function_type(env, [msat_get_bool_type(env)],
                                    msat_get_bool_type(env))
        self.g = msat_declare_function(env, "ltl.G", tp)
        self.f = msat_declare_function(env, "ltl.F", tp)
        self.x = msat_declare_function(env, "ltl.X", tp)
        tp = msat_get_function_type(env, [msat_get_bool_type(env),
                                          msat_get_bool_type(env)],
                                    msat_get_bool_type(env))
        self.u = msat_declare_function(env, "ltl.U", tp)
        self.ltl = set([self.g, self.f, self.x, self.u])

    def X(self, f):
        return msat_make_uf(self.env, self.x, [f])

    def G(self, f):
        return msat_make_uf(self.env, self.g, [f])

    def F(self, f):
        return msat_make_uf(self.env, self.f, [f])

    def U(self, f1, f2):
        return msat_make_uf(self.env, self.u, [f1, f2])

    def is_temporal(self, t):
        return msat_term_get_decl(t) in self.ltl

    def is_X(self, t):
        return msat_term_get_decl(t) == self.x

    def is_G(self, t):
        return msat_term_get_decl(t) == self.g

    def is_F(self, t):
        return msat_term_get_decl(t) == self.f

    def is_U(self, t):
        return msat_term_get_decl(t) == self.u

    def normalize(self, f):
        cache = {}
        def visit(e, t, pre):
            if not pre:
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                if self.is_F(t):
                    tt = self.U(msat_make_true(e), args[0])
                elif self.is_G(t):
                    tt = msat_make_not(e, self.U(msat_make_true(e),
                                                 msat_make_not(e, args[0])))
                else:
                    tt = msat_make_term(e, msat_term_get_decl(t), args)
                cache[t] = tt
            return MSAT_VISIT_PROCESS
        msat_visit_term(self.env, f, visit)
        return cache[f]

    def make_el(self, t):
        d = msat_declare_function(
            self.env, "{EL_%s_%d}" % ('U' if self.is_U(t) else 'X',
                                      msat_term_id(t)),
            msat_get_bool_type(self.env))
        return msat_make_constant(self.env, d)        

    def get_elementary_subformulas(self, f):
        el = []
        def visit(e, t, pre):
            if not pre:
                if self.is_X(t) or self.is_U(t):
                    el.append((t, self.make_el(t)))
            return MSAT_VISIT_PROCESS
        msat_visit_term(self.env, f, visit)
        return el

    def get_constraints(self, f):
        cache = {}
        trans = []
        justice = []
        def visit(e, t, pre):
            if not pre:
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                if self.is_X(t):
                    cache[t] = self.make_el(t)
                    trans.append((cache[t], args[0]))
                elif self.is_U(t):
                    el = self.make_el(t)
                    cache[t] = msat_make_or(e, args[1],
                                            msat_make_and(e, args[0], el))
                    trans.append((el, cache[t]))
                    justice.append(msat_make_or(e, msat_make_not(e, cache[t]),
                                                args[1]))
                else:
                    tt = msat_make_term(e, msat_term_get_decl(t), args)
                    cache[t] = tt
            return MSAT_VISIT_PROCESS
        msat_visit_term(self.env, f, visit)
        return cache, trans, justice

    def make_single_justice(self, justice):
        if len(justice) == 1:
            return justice[0], [], []

        sv = []
        tp = msat_get_bool_type(self.env)
        for j in justice:
            d = msat_declare_function(self.env, '{J%d}' % msat_term_id(j), tp)
            sv.append(msat_make_constant(self.env, d))

        accept = msat_make_true(self.env)
        for v in sv:
            accept = msat_make_and(self.env, accept, v)

        def ite(c, t, e):
            return msat_make_and(
                self.env,
                msat_make_or(self.env, msat_make_not(self.env, c), t),
                msat_make_or(self.env, c, e))
            
        f = msat_make_false(self.env)
        trans = []
        for i, j in enumerate(justice):
            v = sv[i]
            trans.append((v, f, ite(accept, j, msat_make_or(self.env, j, v))))

        return accept, sv, trans

# end of class LtlEncoder


def encode(opts, env, ltl, model):
    if opts.embed_invars:
        invars = []
        for (f, key, val) in model.extra_annotated:
            if key == 'invar':
                invars.append(f)
        if invars:
            log('embedding %d invar constraints', invars)
            invar = reduce(lambda a, b: msat_make_and(env, a, b), invars,
                           msat_make_true(env))
            ninvar = model.next(invar)
            model.init = msat_make_and(env, model.init, invar)
            model.trans = msat_make_and(env, model.trans,
                                        msat_make_and(env, invar, ninvar))
            notinvar = msat_make_not(env, invar)
            for i, p in enumerate(model.props):
                model.props[i] = msat_make_or(env, notinvar, p)

    if opts.single_justice:
        for idx, p in enumerate(model.liveprops):
            if len(p) > 1:
                justice = [msat_make_not(env, j) for j in p]
                fair, extrasv, extratrans = ltl.make_single_justice(justice)
                log('generated single fairness constraint for live property %d',
                    idx)
                for v in extrasv:
                    tp = msat_term_get_type(v)
                    name = str(v) + '.next'
                    n = msat_make_constant(env,
                                           msat_declare_function(env, name, tp))
                    model.add_state_var(v, n)
                for (v, i, n) in extratrans:
                    model.init = msat_make_and(env, model.init,
                                               msat_make_eq(env, v, i))
                    c = msat_make_eq(env, model.next(v), n)
                    model.trans = msat_make_and(env, model.trans, c)

                model.liveprops[idx] = msat_make_not(env, fair)        

    for (f, key, val) in model.extra_annotated:
        if key == 'ltl-property' and opts.ltl_encode:
            f = model.extra_annotated[0][0]
            log('parsed LTL formula: %s', msat_to_smtlib2_term(env, f))
            neg_f = ltl.normalize(msat_make_not(env, f))
            log('normalized and negated: %s', msat_to_smtlib2_term(env, neg_f))
            el = ltl.get_elementary_subformulas(neg_f)
            log('got %d elementary subformulas:', len(el))
            for (t, l) in el:
                log('  %s  <-->  %s', msat_to_smtlib2_term(env, t),
                    msat_to_smtlib2_term(env, l))
            sat, trans, justice = ltl.get_constraints(neg_f)
            log('got %d transition constraints', len(trans))
            for (t, n) in trans:
                log('(= %s (next %s))' % (msat_to_smtlib2_term(env, t),
                                          msat_to_smtlib2_term(env, n)))
            log('got %d fairness constraints', len(justice))
            for j in justice:
                log(msat_to_smtlib2_term(env, j))
            if opts.single_justice:
                fair, extrasv, extratrans = ltl.make_single_justice(justice)
                log('generated single fairness constraint')
            else:
                fair, extrasv, extratrans = None, [], []
            # now add to the model
            sv = [l for (t, l) in el] + extrasv
            for v in sv:
                tp = msat_term_get_type(v)
                name = str(v) + '.next'
                n = msat_make_constant(env,
                                       msat_declare_function(env, name, tp))
                model.add_state_var(v, n)
            # initial constraints
            model.init = msat_make_and(env, model.init, sat[neg_f])
            # add the transition relation
            for (t, n) in trans:
                c = msat_make_eq(env, t, model.next(n))
                model.trans = msat_make_and(env, model.trans, c)
            for (v, i, n) in extratrans:
                model.init = msat_make_and(env, model.init,
                                           msat_make_eq(env, v, i))
                c = msat_make_eq(env, model.next(v), n)
                model.trans = msat_make_and(env, model.trans, c)
            # and the new property
            if opts.single_justice:
                model.liveprops.append(msat_make_not(env, fair))
            else:
                model.liveprops.append([msat_make_not(env, j) for j in justice])
            log('added the tableau and live property %d to the model',
                len(model.liveprops)-1)

    if opts.remove_extended:
        extra = []
        for t in model.extra_annotated:
            key = t[1]
            if (opts.embed_invars and key == 'invar') or \
               (opts.ltl_encode and key == 'ltl-property'):
                pass
            else:
                extra.append(t)
        model.extra_annotated = extra


def getopts():
    p = argparse.ArgumentParser()
    def add_flag(f, help):
        p.add_argument('--no-%s' % f, action='store_false',
                       dest=f.replace('-', '_'))
        p.add_argument('--%s' % f, action='store_true',
                       help=help + ' (default: true)', default=True)
    add_flag('embed-invars', 'embed invar constraints in the transition system')
    add_flag('ltl-encode', 'encode LTL properties as live properties')
    add_flag('single-justice',
             'convert multiple fairness constraints into a single one')
    add_flag('remove-extended', 'remove extended annotations')
    p.add_argument('-v', '--verbose', action='store_true', default=False)
    ret = p.parse_args()
    global _verb
    _verb = ret.verbose
    return ret


def main():
    opts = getopts()
    env = msat_create_env({'allow_bool_function_args' : 'true'})
    ltl = LtlEncoder(env)
    log('reading vmt model from stdin')
    model = vmt.read(env, sys.stdin)
    encode(opts, env, ltl, model)
    vmt.write(model, sys.stdout)
    msat_destroy_env(env)
 
 

if __name__ == '__main__':
    main()
