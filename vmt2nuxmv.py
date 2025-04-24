#!/usr/bin/env python

##  Copyright (c) 2018-2021 Alberto Griggio <griggio@fbk.eu>
##
##  This is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This software is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this software.  If not, see <http://www.gnu.org/licenses/>.

from mathsat import *
import vmt
import os, sys
from email.utils import quote
import time


class Unsupported(Exception):
    def __init__(self, op):
        super(Unsupported, self).__init__(op)
        self.op = op


def to_transcendental(t):
    name = msat_decl_get_name(msat_term_get_decl(t))
    tmap = {
        '.exp' : 'exp',
        '.sin' : 'sin',
        '.cos' : 'cos',
        '.tan' : 'tan'
        }
    func = tmap.get(name)
    if func is None:
        def f(a):
            raise Unsupported(name)
    else:
        def f(a):
            return '%s(%s)' % (func, a[0])
    return f


def to_nuxmv(model, out):
    pr = out.write
    env = model.env

    def fix_name(name):
        name = '"%s"' % quote(name)
        return name

    def type_recur(tp):
        if msat_is_bool_type(env, tp):
            t = 'boolean'
        elif msat_is_rational_type(env, tp):
            t = 'real'
        elif msat_is_integer_type(env, tp):
            t = 'integer'
        else:
            ok, w = msat_is_bv_type(env, tp)
            if ok:
                t = 'word[%d]' % w
            else:
                ok, itp, etp = msat_is_array_type(env, tp)
                if ok:
                    idx = type_recur(itp)
                    elem = type_recur(etp)
                    t = 'array %s of %s' % (idx, elem)
                else:
                    assert False
        return t 
        
    def declare_var(v):
        d = msat_term_get_decl(v)
        name = msat_decl_get_name(d)
        tp = msat_decl_get_return_type(d)
        pr('%s : %s;\n' % (fix_name(name), type_recur(tp)))

    cache = {
        msat_make_true(env) : 'TRUE',
        msat_make_false(env) : 'FALSE',
        }

    ivars = []
    def visit_ivars(e, t, pre):
        if not pre and msat_term_is_constant(e, t) and t not in model.curvars \
           and t not in model.nextvars:
            ivars.append(t)
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, model.trans, visit_ivars)
    ivars.sort(key=msat_term_id)

    for v in ivars:
        name = msat_decl_get_name(msat_term_get_decl(v))
        cache[v] = fix_name(name)
    for (c, n) in model.statevars:
        name = msat_decl_get_name(msat_term_get_decl(c))
        cache[c] = fix_name(name)
        cache[n] = 'next(' + fix_name(name) + ')'

    defn = [1]
    defs = []

    def unsupported(op):
        def f(a):
            raise Unsupported(op)
        return f
    special = object()
    
    tagmap = {
        MSAT_TAG_TRUE: lambda a: 'TRUE',
        MSAT_TAG_FALSE: lambda a: 'FALSE',
        MSAT_TAG_AND: lambda a: '%s & %s' % (a[0], a[1]),
        MSAT_TAG_OR: lambda a: '%s | %s' % (a[0], a[1]),
        MSAT_TAG_NOT: lambda a: '! %s' % a[0],
        MSAT_TAG_IFF: lambda a: '%s <-> %s' % (a[0], a[1]),
        MSAT_TAG_PLUS: lambda a: '%s + %s' % (a[0], a[1]),
        MSAT_TAG_TIMES: lambda a: '%s * %s' % (a[0], a[1]),
        MSAT_TAG_FLOOR: unsupported("floor"),
        MSAT_TAG_LEQ: lambda a: '%s <= %s' % (a[0], a[1]),
        MSAT_TAG_EQ: lambda a: '%s = %s' % (a[0], a[1]),
        MSAT_TAG_ITE: lambda a: '(case %s: %s; TRUE: %s; esac)' % (a[0], a[1],
                                                                   a[2]),
        MSAT_TAG_INT_MOD_CONGR: unsupported("int mod congr"),
        MSAT_TAG_BV_CONCAT: lambda a: '%s :: %s' % (a[0], a[1]),
        MSAT_TAG_BV_EXTRACT: special,
        MSAT_TAG_BV_NOT: lambda a: '! %s' % a[0],
        MSAT_TAG_BV_AND: lambda a: '%s & %s' % (a[0], a[1]),
        MSAT_TAG_BV_OR: lambda a: '%s | %s' % (a[0], a[1]),
        MSAT_TAG_BV_XOR: lambda a: '%s xor %s' % (a[0], a[1]),
        MSAT_TAG_BV_ULT: lambda a: '%s < %s' % (a[0], a[1]),
        MSAT_TAG_BV_SLT: lambda a: 'signed(%s) < signed(%s)' % (a[0], a[1]),
        MSAT_TAG_BV_ULE: lambda a: '%s <= %s' % (a[0], a[1]),
        MSAT_TAG_BV_SLE: lambda a: 'signed(%s) <= signed(%s)' % (a[0], a[1]),
        MSAT_TAG_BV_COMP: lambda a: 'word1(%s = %s)' % (a[0], a[1]),
        MSAT_TAG_BV_NEG: lambda a: '- %s' % a[0],
        MSAT_TAG_BV_ADD: lambda a: '%s + %s' % (a[0], a[1]),
        MSAT_TAG_BV_SUB: lambda a: '%s - %s' % (a[0], a[1]),
        MSAT_TAG_BV_MUL: lambda a: '%s * %s' % (a[0], a[1]),
        MSAT_TAG_BV_UDIV: lambda a: '%s / %s' % (a[0], a[1]),
        MSAT_TAG_BV_SDIV:
        lambda a: 'unsigned(signed(%s) / signed(%s))' % (a[0], a[1]),
        MSAT_TAG_BV_UREM: lambda a: '%s mod %s' % (a[0], a[1]),
        MSAT_TAG_BV_SREM:
        lambda a: 'unsigned(signed(%s) mod signed(%s))' % (a[0], a[1]),
        MSAT_TAG_BV_LSHL: lambda a: '%s << %s' % (a[0], a[1]),
        MSAT_TAG_BV_LSHR: lambda a: '%s >> %s' % (a[0], a[1]),
        MSAT_TAG_BV_ASHR: lambda a: 'unsigned(signed(%s) >> %s)' % (a[0], a[1]),
        MSAT_TAG_BV_ROL: unsupported("bv rol"),
        MSAT_TAG_BV_ROR: unsupported("bv ror"),
        MSAT_TAG_BV_ZEXT: special,
        MSAT_TAG_BV_SEXT: special,
        MSAT_TAG_ARRAY_READ: lambda a: 'READ(%s, %s)' % (a[0], a[1]),
        MSAT_TAG_ARRAY_WRITE: lambda a: 'WRITE(%s, %s, %s)' % (a[0], a[1], a[2]),
        MSAT_TAG_FP_EQ: unsupported("fp eq"),
        MSAT_TAG_FP_LT: unsupported("fp lt"),
        MSAT_TAG_FP_LE: unsupported("fp le"),
        MSAT_TAG_FP_NEG: unsupported("fp neg"),
        MSAT_TAG_FP_ADD: unsupported("fp add"),
        MSAT_TAG_FP_SUB: unsupported("fp sub"),
        MSAT_TAG_FP_MUL: unsupported("fp mul"),
        MSAT_TAG_FP_DIV: unsupported("fp div"),
        MSAT_TAG_FP_CAST: unsupported("fp cast"),
        MSAT_TAG_FP_FROM_SBV: unsupported("fp from sbv"),
        MSAT_TAG_FP_FROM_UBV: unsupported("fp from ubv"),
        MSAT_TAG_FP_TO_BV: unsupported("fp to bv"),
        MSAT_TAG_FP_AS_IEEEBV: unsupported("fp as ieeebv"),
        MSAT_TAG_FP_ISNAN: unsupported("fp isnan"),
        MSAT_TAG_FP_ISINF: unsupported("fp isinf"),
        MSAT_TAG_FP_ISZERO: unsupported("fp iszero"),
        MSAT_TAG_FP_ISSUBNORMAL: unsupported("fp issubnormal"),
        MSAT_TAG_FP_FROM_IEEEBV: unsupported("fp from ieeebv"),
        MSAT_TAG_UNKNOWN: special,
        }
        

    def translate(term):
        def visit(e, t, pre):
            if t in cache:
                return MSAT_VISIT_SKIP
            if not pre:
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]

                if msat_term_is_number(e, t):
                    val = msat_term_to_number(e, t)
                    ok, w = msat_is_bv_type(e, msat_term_get_type(t))
                    if ok:
                        val = '0ud%d_%s' % (w, val)
                    else:
                        val = str(val)
                        if '/' in val:
                            val = "f'%s" % val if not val.startswith('-') \
                                  else "-f'%s" % val[1:]
                    cache[t] = val

                else:
                    tag = msat_decl_get_tag(env, msat_term_get_decl(t))
                    func = tagmap.get(tag, unsupported)

                    idx = defn[0]
                    defn[0] += 1
                    ret = '__expr%d' % idx

                    if func is special:
                        if tag == MSAT_TAG_UNKNOWN:
                            func = to_transcendental(t)
                        elif tag == MSAT_TAG_BV_EXTRACT:
                            ok, l, h = msat_term_is_bv_extract(e, t)
                            assert ok
                            func = lambda a: '%s[%d:%d]' % (a[0], l, h)
                        elif tag == MSAT_TAG_BV_SEXT:
                            ok, w = msat_term_is_bv_sext(e, t)
                            assert ok
                            ok, ww = msat_is_bv_type(e, msat_term_get_type(t))
                            assert ok
                            ww -= w
                            if ww:
                                func = lambda a: \
                                       '(case signed(%s) < signed(0ud%d_0) : ' \
                                       '0ud%d_1; TRUE: 0ud%d_0; esac) :: %s' % \
                                       (a[0], ww, w, w, a[0])
                            else:
                                func = lambda a: a[0]
                        elif tag == MSAT_TAG_BV_ZEXT:
                            ok, w = msat_term_is_bv_zext(e, t)
                            func = lambda a: '0ud%d_0 :: %s' % (w, a[0])
                            assert ok
                    
                    try:
                        defs.append('%s := %s;' % (ret, func(args)))
                    except Exception:
                        sys.stderr.write('UNSUPPORTED TAG: %s\n' % tag)
                        raise
                    cache[t] = ret
                
            return MSAT_VISIT_PROCESS
        
        msat_visit_term(env, term, visit)

    translate(model.init)
    translate(model.trans)
    for prop in model.props:
        translate(prop)
    for prop in model.liveprops:
        for j in prop:
            translate(j)

    pr('-- generated by %s on %s\n' %
       (os.path.basename(sys.argv[0]), time.ctime()))
    pr('MODULE main\n')
    if ivars:
        pr('IVAR\n')
        for v in ivars:
            declare_var(v)
        pr('\n')

    if model.statevars:
        pr('VAR\n')
        for (c, n) in model.statevars:
            declare_var(c)
        pr('\n')

    if defs:
        pr('DEFINE\n')
        for d in defs:
            pr(d)
            pr('\n')
        pr('\n')

    pr('INIT %s;\n' % cache[model.init])
    pr('TRANS %s;\n' % cache[model.trans])
    for prop in model.props:
        pr('INVARSPEC %s;\n' % cache[prop])
    for prop in model.liveprops:
        pr('LTLSPEC ')
        sep = ''
        for j in prop:
            pr(sep)
            pr('F G (%s)' % cache[j])
            sep = ' | '
        pr(';\n')


def main():
    env = msat_create_env()
    #model = vmt.read(env, "/data/guangyuh/coding_env/horn2vmt/bin/ssft_simple_1.vmt")
    model = vmt.read(env, "/data/guangyuh/coding_env/vmt-tools/vmt-tools-0.4/a02.vmt")
    try:
        to_nuxmv(model, sys.stdout)
    except Unsupported as e:
        sys.stderr.write("ERROR: unsupported operation: %s\n" % e.op)
    msat_destroy_env(env)


if __name__ == '__main__':
    main()
