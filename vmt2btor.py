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

import os, sys
from mathsat import *
import vmt
import math, time


class Unsupported(Exception):
    def __init__(self, op):
        super(Unsupported, self).__init__(op)
        self.op = op


def to_btor(env, model, out):
    lines = []
    pr = lines.append

    def fix_name(name):
        name = name.replace(' ', '_').replace(';', '_')
        return name

    btorid = [0]
    def getid():
        btorid[0] += 1
        return btorid[0]

    def gettp(tp):
        if msat_is_bool_type(env, tp):
            return (1, None)
        elif msat_is_bv_type(env, tp)[0]:
            _, w = msat_is_bv_type(env, tp)
            return (w, None)
        elif msat_is_array_type(env, tp)[0]:
            _, it, et = msat_is_array_type(env, tp)
            return (gettp(it), gettp(et))
        else:
            raise Unsupported("unsupported type: %s" % msat_type_repr(tp))

    sortmap = {}
    zeromap = {}
    def declare_sort(s):
        i = getid()
        sortmap[s] = i
        if s[1] is not None:
            if s[0] not in sortmap:
                declare_sort(s[0])
            if s[1] not in sortmap:
                declare_sort(s[1])
            pr('%d sort array %d %d\n' % (i, sortmap[s[0]], sortmap[s[1]]))
        else:
            pr('%d sort bitvec %d\n' % (i, s[0]))
            z = getid()
            pr('%d zero %d\n' % (z, i))
            zeromap[s] = z

    allnames = set()
    def declare_var(d, name, is_state):
        tp = gettp(msat_decl_get_return_type(d))
        sid = sortmap[tp]
        i = getid()
        kind = 'state' if is_state else 'input'
        pr('%d %s %d %s\n' % (i, kind, sid, fix_name(name)))
        allnames.add(name)
        return i

    def mkname(name):
        bn = name
        i = 1
        while name in allnames:
            name = '%s.%d' % (bn, i)
            i += 1
        return name

    declare_sort((1, None))

    allvars = set()
    def visit_getvars(e, t, pre):
        if pre and msat_term_is_constant(e, t):
            allvars.add(t)
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, model.init, visit_getvars)
    msat_visit_term(env, model.trans, visit_getvars)
    for p in model.props:
        msat_visit_term(env, p, visit_getvars)
    for p in model.liveprops:
        msat_visit_term(env, p, visit_getvars)
    for (c, n) in model.statevars:
        allvars.add(c)
        allvars.add(n)

    allvars = sorted(allvars, key=msat_term_id)
    for v in allvars:
        tp = msat_term_get_type(v)
        s = gettp(tp)
        if s not in sortmap:
            declare_sort(s)

    bid = getid()
    pr('%d constd 1 1\n' % bid)
    nbid = getid()
    pr('%d not 1 %d\n' % (nbid, bid))
    cache = {
        msat_make_true(env) : bid,
        msat_make_false(env) : nbid,
        }

    for v in allvars:
        is_state = v in model.curvars
        d = msat_term_get_decl(v)
        name = msat_decl_get_name(d)
        cache[v] = declare_var(d, name, is_state)
    for (c, n) in model.statevars:
        s = gettp(msat_term_get_type(c))
        sid = sortmap[s]
        try:
            vid = cache[c]
        except KeyError:
            print('ERROR: %s %s' % (c, c in allvars))
            raise
        nid = cache[n]
        
        if s[1] is None:
            z = zeromap[s]
            pr('%d init %d %d %d\n' % (getid(), sid, vid, z))
        pr('%d next %d %d %d\n' % (getid(), sid, vid, nid))
            

    def unsupported(op):
        def f(a):
            raise Unsupported(op)
        return f

    def tag_ite(t, a):
        return ('ite',) + tuple(a)

    def tag_extract(t, a):
        ok, h, l = msat_term_is_bv_extract(env, t)
        assert ok
        return ('slice', a[0], h, l)

    def tag_log2_op(op):
        def f(t, a):
            w = gettp(msat_term_get_type(msat_term_get_arg(t, 0)))[0]
            n = math.log(w, 2)
            n2 = int(math.ceil(n))
            if n2 > n:
                ww = 2**n2
                i = getid()
                sw = (ww-w, None)
                if sw not in sortmap:
                    declare_sort(sw)
                sww = (ww, None)
                if sww not in sortmap:
                    declare_sort(sww)
                pr('%d constd %d 0\n' % (i, sortmap[sw]))
                ii = getid()
                pr('%d concat %d %d %d\n' % (ii, sortmap[sww], i, a[0]))
                a[0] = ii
                w = ww
            i = getid()
            sn2 = (n2, None)
            if sn2 not in sortmap:
                declare_sort(sn2)
            pr('%d slice %d %d %d 0\n' % (i, sortmap[sn2], a[1], n2-1))
            a[1] = i
            if n2 > n:
                i = getid()
                sn22 = (2**n2, None)
                if sn22 not in sortmap:
                    declare_sort(sn22)
                pr('%d %s %d %d %d\n' % (i, op, sortmap[sn22], a[0], a[1]))
                return ('slice', i, w-1, 0)
            else:
                return (op, a[0], a[1])
        return f

    def tag_zext(t, a):
        _, ww = msat_term_is_bv_zext(env, t)
        return ('uext', a[0], ww)

    def tag_sext(t, a):
        _, ww = msat_term_is_bv_sext(env, t)
        return ('sext', a[0], ww)

    tagmap = {
        MSAT_TAG_AND: lambda t, a: ('and', a[0], a[1]),
        MSAT_TAG_OR: lambda t, a: ('or', a[0], a[1]),
        MSAT_TAG_NOT: lambda t, a: ('not', a[0]),
        MSAT_TAG_IFF: lambda t, a: ('eq', a[0], a[1]),
        MSAT_TAG_PLUS: unsupported("+"),
        MSAT_TAG_TIMES: unsupported("*"),
        MSAT_TAG_FLOOR: unsupported("floor"),
        MSAT_TAG_LEQ: unsupported("<="),
        MSAT_TAG_EQ: lambda t, a: ('eq', a[0], a[1]),
        MSAT_TAG_ITE: tag_ite,
        MSAT_TAG_INT_MOD_CONGR: unsupported("int mod congr"),
        MSAT_TAG_BV_CONCAT: lambda t, a: ('concat', a[0], a[1]),
        MSAT_TAG_BV_EXTRACT: tag_extract,
        MSAT_TAG_BV_NOT: lambda t, a: ('not', a[0]),
        MSAT_TAG_BV_AND: lambda t, a: ('and', a[0], a[1]),
        MSAT_TAG_BV_OR: lambda t, a: ('or', a[0], a[1]),
        MSAT_TAG_BV_XOR: lambda t, a: ('xor', a[0], a[1]),
        MSAT_TAG_BV_ULT: lambda t, a: ('ult', a[0], a[1]),
        MSAT_TAG_BV_SLT: lambda t, a: ('slt', a[0], a[1]),
        MSAT_TAG_BV_ULE: lambda t, a: ('ulte', a[0], a[1]),
        MSAT_TAG_BV_SLE: lambda t, a: ('slte', a[0], a[1]),
        MSAT_TAG_BV_COMP: lambda t, a: ('eq', a[0], a[1]),
        MSAT_TAG_BV_NEG: lambda t, a: ('neg', a[0]),
        MSAT_TAG_BV_ADD: lambda t, a: ('add', a[0], a[1]),
        MSAT_TAG_BV_SUB: lambda t, a: ('sub', a[0], a[1]),
        MSAT_TAG_BV_MUL: lambda t, a: ('mul', a[0], a[1]),
        MSAT_TAG_BV_UDIV: lambda t, a: ('udiv', a[0], a[1]),
        MSAT_TAG_BV_SDIV: lambda t, a: ('sdiv', a[0], a[1]),
        MSAT_TAG_BV_UREM: lambda t, a: ('urem', a[0], a[1]),
        MSAT_TAG_BV_SREM: lambda t, a: ('srem', a[0], a[1]),
        MSAT_TAG_BV_LSHL: tag_log2_op('sll'),
        MSAT_TAG_BV_LSHR: tag_log2_op('srl'),
        MSAT_TAG_BV_ASHR: tag_log2_op('sra'),
        MSAT_TAG_BV_ROL: tag_log2_op('rol'),
        MSAT_TAG_BV_ROR: tag_log2_op('ror'),
        MSAT_TAG_BV_ZEXT: tag_zext,
        MSAT_TAG_BV_SEXT: tag_sext,
        MSAT_TAG_ARRAY_READ: lambda t, a: ('read', a[0], a[1]),
        MSAT_TAG_ARRAY_WRITE: lambda t, a: ('write', a[0], a[1], a[2]),
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
                    ok, _ = msat_is_bv_type(e, msat_term_get_type(t))
                    if ok:
                        tp = gettp(msat_term_get_type(t))
                        if tp not in sortmap:
                            declare_sort(tp)
                        i = getid()
                        sid = sortmap[tp]
                        pr('%d constd %d %s\n' % (i, sid, val))
                        val = i
                    else:
                        raise Unsupported("unsupported type: %s" %
                                          msat_type_repr(msat_term_get_type(t)))
                    cache[t] = val

                else:
                    tag = msat_decl_get_tag(env, msat_term_get_decl(t))
                    func = tagmap.get(tag, unsupported)

                    val = func(t, args)
                    idx = getid()
                    tp = gettp(msat_term_get_type(t))
                    if tp not in sortmap:
                        declare_sort(tp)
                    sid = sortmap[tp]
                    pr('%d %s %s %s\n' % (idx, val[0],
                                          sid, ' '.join(map(str, val[1:]))))
                    cache[t] = idx
                
            return MSAT_VISIT_PROCESS
        
        msat_visit_term(env, term, visit)

    tinit = model.next(model.init)
    pr('; init\n')
    translate(tinit)
    pr('; trans\n')
    translate(model.trans)

    pr('; reset sequence\n')
    true_id = cache[msat_make_true(env)]
    false_id = cache[msat_make_false(env)]
    reset0 = getid()
    pr('%d state 1 %s\n' % (reset0, mkname("model-reset0")))
    pr('%d init 1 %d %d\n' % (getid(), reset0, false_id))
    pr('%d next 1 %d %d\n' % (getid(), reset0, true_id))
    reset1 = getid()
    pr('%d state 1 %s\n' % (reset1, mkname("model-reset1")))
    pr('%d init 1 %d %d\n' % (getid(), reset1, false_id))
    pr('%d next 1 %d %d\n' % (getid(), reset1, reset0))
    nreset1 = getid()
    first = getid()
    pr('%d not 1 %d\n' % (nreset1, reset1))
    pr('%d and 1 %d %d\n' % (first, reset0, nreset1))    

    pr('; model var\n')
    modelvar = getid()
    pr('%d state 1 %s\n' % (modelvar, mkname("model-valid")))
    pr('%d init 1 %d %d\n' % (getid(), modelvar, false_id))
    init = cache[tinit]
    trans = cache[model.trans]
    step = getid()
    modelval = getid()
    pr('%d and 1 %d %d\n' % (step, modelvar, trans))
    pr('%d ite 1 %d %d %d\n' % (modelval, first, init, step))
    ok = getid()
    pr('%d ite 1 %d %d %d\n' % (ok, reset0, modelval, false_id))
    pr('%d next 1 %d %d\n' % (getid(), modelvar, ok))

    for i, p in enumerate(model.props):
        pr('; property %d\n' % i)
        translate(p)
        p = cache[p]
        np = getid()
        r = getid()
        pr('%d not 1 %d\n' % (np, p))
        pr('%d and 1 %d %d\n' % (r, modelvar, np))
        pr('%d bad %d\n' % (getid(), r))
    if model.liveprops:
        pr('; WARNING: live properties not supported yet!\n')

    write = sys.stdout.write
    write('; generated by %s on %s\n' %
          (os.path.basename(sys.argv[0]), time.ctime()))
    for line in lines:
        write(line)
    

def main():
    env = msat_create_env()
    #model = vmt.read(env, "/data/guangyuh/coding_env/horn2vmt/bin/ssft_simple_1.vmt")
    model = vmt.read(env, "/Users/huguangyu/coding_env/ivybench/distai/vmt/Ricart-Agrawala.vmt")
    #model = vmt.read(env, "/data/guangyuh/coding_env/vmt-tools/vmt-tools-0.4/a02.vmt")
    try:
        to_btor(env, model, sys.stdout)
    except Unsupported as e:
        sys.stderr.write("ERROR: unsupported operation: %s\n" % e.op)
    msat_destroy_env(env)


if __name__ == '__main__':
    main()
