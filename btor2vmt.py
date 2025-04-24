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
import vmt
from mathsat import *
import time
from collections import OrderedDict as odict


bvcontext = 0
boolcontext = 1


class Register(object):
    def __init__(self, name, v, init, next):
        self.name = name
        self.var = v
        self.init = init
        self.next = next

# end of class Register


class Input(object):
    def __init__(self, name, v):
        self.name = name
        self.var = v

# end of class Input


class BTORConverter(object):
    def __init__(self, env):
        self.symtbl_ = {}
        self.novar_ = object()
        self.env = env
        self.sorts_ = {}
        self.registers = odict()
        self.inputs = odict()
        self.bads = []
        self.constraints = []
        self.outputs = []

    def get(self, idx, context):
        t = self.symtbl_[abs(idx)][context]
        if idx < 0:
            if context == boolcontext:
                t = msat_make_not(self.env, t)
            else:
                t = msat_make_bv_not(self.env, t)
        return t

    def set(self, idx, term, tp):
        assert idx not in self.symtbl_
        if self.is_bool_(tp):
            tt = msat_make_term_ite(self.env, term,
                                    msat_make_bv_number(self.env, "1", 1, 10),
                                    msat_make_bv_number(self.env, "0", 1, 10))
            if not MSAT_ERROR_TERM(tt):
                t2 = term
                term = tt
            else:
                t2 = msat_make_equal(self.env, term,
                                     msat_make_bv_number(self.env, "1", 1, 10))
        else:
            t2 = self.novar_
        self.symtbl_[idx] = (term, t2)

    def set_init(self, sort, v, e):
        if self.is_bool_(sort):
            tt = self.get(e, boolcontext)
        else:
            tt = self.get(e, bvcontext)
        self.registers[v].init = tt

    def set_next(self, sort, v, e):
        if self.is_bool_(sort):
            tt = self.get(e, boolcontext)
        else:
            tt = self.get(e, bvcontext)
        self.registers[v].next = tt

    def is_bool_(self, tp):
        return msat_is_bool_type(self.env, self.sorts_[tp])

    def mk_bv_sort(self, idx, w):
        if w == 1:
            tp = msat_get_bool_type(self.env)
        else:
            tp = msat_get_bv_type(self.env, w)
        self.sorts_[idx] = tp

    def mk_array_sort(self, idx, s1, s2):
        i = self.get_type_(s1)
        e = self.get_type_(s2)
        a = msat_get_array_type(self.env, i, e)
        self.sorts_[idx] = a

    def mk_var(self, prefix, idx, name, tp):
        assert idx not in self.symtbl_
        if not name:
            name = "%s[]" % prefix
        else:
            name = "%s[%s]" % (prefix, name)
        d = msat_declare_function(self.env, name, self.get_type_(tp))
        v = msat_make_constant(self.env, d)
        if self.is_bool_(tp):
            vv = v
            v = msat_make_term_ite(self.env, v,
                                   msat_make_bv_number(self.env, "1", 1, 10),
                                   msat_make_bv_number(self.env, "0", 1, 10))
        else:
            vv = self.novar_
        self.symtbl_[idx] = (v, vv)

    def mk_state(self, idx, name, tp):
        self.mk_var("s%d" % len(self.registers), idx, name, tp)
        v = self.get(idx, boolcontext if self.is_bool_(tp) else bvcontext)
        self.registers[idx] = Register(name, v, None, None)

    def mk_input(self, idx, name, tp):
        self.mk_var("i%d" % len(self.inputs), idx, name, tp)
        v = self.get(idx, boolcontext if self.is_bool_(tp) else bvcontext)
        self.inputs[idx] = Input(name, v)

    def get_type_(self, tp):
        return self.sorts_[tp]

    def add_bad(self, idx):
        r = self.get(idx, boolcontext)
        self.bads.append(r)

    def add_constraint(self, idx):
        r = self.get(idx, boolcontext)
        self.constraints.append(r)

    def add_output(self, idx):
        r = self.get(idx, bvcontext)
        self.outputs.append(r)

    def _to_trans(self):
        if not self.registers:
            raise Exception('no registers')
        
        env = self.env
        init, trans, prop = None, None, None
        statevars = []

        init = msat_make_true(env)
        trans = msat_make_true(env)
        sv = set()
        for idx in self.registers:
            reg = self.registers[idx]
            d = msat_term_get_decl(reg.var)
            n = msat_decl_get_name(d)
            nn = n + ".next"
            assert MSAT_ERROR_DECL(msat_find_decl(env, nn))
            dd = msat_declare_function(env, nn, msat_term_get_type(reg.var))
            vn = msat_make_constant(env, dd)
            statevars.append((reg.var, vn))
            sv.add(reg.var)
            if reg.init is not None:
                regtp = msat_term_get_type(reg.var)
                yes, idx, elem = msat_is_array_type(env, regtp)
                if yes and msat_type_equals(elem,
                                            msat_term_get_type(reg.init)):
                    e = msat_make_eq(env, reg.var,
                                     msat_make_array_const(env, regtp,
                                                           reg.init))
                else:
                    e = msat_make_eq(env, reg.var, reg.init)
                assert not MSAT_ERROR_TERM(e), (str(reg.var), str(reg.init))
                init = msat_make_and(env, init, e)
            if reg.next is not None:
                e = msat_make_eq(env, vn, reg.next)
                trans = msat_make_and(env, trans, e)

        constr = msat_make_true(env)
        need_elim = False
        for c in self.constraints:
            if not is_input_constr(env, c, sv):
                need_elim = True
            constr = msat_make_and(env, constr, c)
        iconstr = msat_make_true(env)
        removed = set()
        if need_elim:
            iconstr, removed = elim_inputs(env, constr, sv)
        trans = msat_make_and(env, trans, constr)

        if not self.bads:
            prop = msat_make_true(env)
        else:
            assert len(self.bads) == 1
            bad = self.bads[0]
            prop = msat_make_not(env, bad)

        init, prop = add_constraint(env, init, prop, constr, iconstr,
                                    removed)

        statevars = ensure_state_vars(env, init, prop, statevars)

        return vmt.Model(self.env, statevars, init, trans, [prop])

    def _to_formula(self):
        if self.registers:
            raise Exception('registers found')

        formula = msat_make_true(env)
        for r in btor.outputs:
            formula = msat_make_and(env, formula, r)
        return formula

    def to_vmt(self, out):
        model = self._to_trans()
        out.write(';; generated by %s on %s\n' %
                  (os.path.basename(sys.argv[0]), time.ctime()))
        vmt.write(model, out)

    def to_smt(self, out):
        formula = self._to_formula()
        out.write(msat_to_smtlib2(self.env, formula))        

# end of class BTORConverter


def make_xor(env, t1, t2):
    return msat_make_not(env, msat_make_iff(env, t1, t2))

def make_xnor(env, t1, t2):
    return msat_make_not(env, make_xor(env, t1, t2))

def make_bv_xnor(env, t1, t2):
    return msat_make_bv_not(env, msat_make_bv_xor(env, t1, t2))    

def make_implies(env, t1, t2):
    return msat_make_or(env, msat_make_not(env, t1), t2)

def make_bv_implies(env, t1, t2):
    return msat_make_bv_or(env, msat_make_bv_not(env, t1), t2)

def parse_bool_connective(boolop, bvop):
    assert bvop is not None
    if bvop is None:
        def func(btor, idx, w, a1, a2, *rest):
            btor.set(idx, boolop(btor.env, btor.get(a1, boolcontext),
                                 btor.get(a2, boolcontext)), w)
    else:
        def func(btor, idx, w, a1, a2, *rest):
            if btor.is_bool_(w):
                t1 = btor.get(a1, boolcontext)
                t2 = btor.get(a2, boolcontext)
                term = boolop(btor.env, t1, t2)
            else:
                term = bvop(btor.env, btor.get(a1, bvcontext),
                            btor.get(a2, bvcontext))
            btor.set(idx, term, w)
    return func


def parse_not(btor, idx, w, a, *rest):
    if btor.is_bool_(w):
        term = msat_make_not(btor.env, btor.get(a, boolcontext))
    else:
        term = msat_make_bv_not(btor.env, btor.get(a, bvcontext))
    btor.set(idx, term, w)


def parse_cond(btor, idx, w, a1, a2, a3, *rest):
    c = btor.get(a1, boolcontext)
    if btor.is_bool_(w):
        t = btor.get(a2, boolcontext)
        e = btor.get(a3, boolcontext)
        term = msat_make_and(btor.env,
                             msat_make_or(btor.env,
                                          msat_make_not(btor.env, c), t),
                             msat_make_or(btor.env, c, e))
    else:
        t = btor.get(a2, bvcontext)
        e = btor.get(a3, bvcontext)
        term = msat_make_term_ite(btor.env, c, t, e)
    btor.set(idx, term, w)


def parse_bv_neg(btor, idx, w, a, *rest):
    term = msat_make_bv_neg(btor.env, btor.get(a, bvcontext))
    btor.set(idx, term, w)
    

def parse_bv_op(bvop):
    def func(btor, idx, w, a1, a2, *rest):
        term = bvop(btor.env, btor.get(a1, bvcontext), btor.get(a2, bvcontext))
        assert not MSAT_ERROR_TERM(term)
        btor.set(idx, term, w)
    return func


def parse_equal(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)

    term = msat_make_eq(btor.env, t1, t2)
    btor.set(idx, term, w)


def parse_not_equal(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)

    term = msat_make_eq(btor.env, t1, t2)
    term1 = msat_make_not(btor.env, term)
    btor.set(idx, term1, w)


def parse_bv_shift(bvop):
    def func(btor, idx, w, a1, a2, *rest):
        t1 = btor.get(a1, bvcontext)
        t2 = btor.get(a2, bvcontext)
        ok, w1 = msat_is_bv_type(btor.env, btor.get_type_(w))
        assert ok
        ok, w2 = msat_is_bv_type(btor.env, msat_term_get_type(t2))
        assert ok
        if w2 < w1:
            t2 = msat_make_bv_zext(btor.env, w1 - w2, t2)
        term = bvop(btor.env, t1, t2)
        assert not MSAT_ERROR_TERM(term)
        btor.set(idx, term, w)
    return func


def parse_bv_slice(btor, idx, w, a, u, l, *rest):
    arg = btor.get(a, bvcontext)
    term = msat_make_bv_extract(btor.env, u, l, arg)
    btor.set(idx, term, w)


def parse_input(btor, idx, sort, name="", *rest):
    btor.mk_input(idx, name, sort)


def parse_state(btor, idx, sort, name="", *rest):
    btor.mk_state(idx, name, sort)


def parse_sort(btor, idx, name, w1, w2=None, *rest):
    if name == 'bitvec':
        btor.mk_bv_sort(idx, w1)
    else:
        assert name == 'array'
        assert w2 is not None
        btor.mk_array_sort(idx, w1, w2)


def parse_bv_number(base):
    def func(btor, idx, tp, value, *rest):
        val = int(str(value), base)
        if btor.is_bool_(tp): #w == 1:
            if val: term = msat_make_true(btor.env)
            else: term = msat_make_false(btor.env)
        else:
            ok, w = msat_is_bv_type(btor.env, btor.get_type_(tp))
            assert ok
            term = msat_make_bv_number(btor.env, str(val), w, 10)
        btor.set(idx, term, tp)
    return func


def parse_zero(btor, idx, tp, *rest):
    if btor.is_bool_(tp): #w == 1:
        term = msat_make_false(btor.env)
    else:
        ok, w = msat_is_bv_type(btor.env, btor.get_type_(tp))
        assert ok
        term = msat_make_bv_number(btor.env, "0", w, 10)
    btor.set(idx, term, tp)


def parse_one(btor, idx, tp, *rest):
    if btor.is_bool_(tp):
        term = msat_make_true(btor.env)
    else:
        ok, w = msat_is_bv_type(btor.env, btor.get_type_(tp))
        assert ok
        term = msat_make_bv_number(btor.env, "1", w, 10)
    btor.set(idx, term, tp)


def parse_ones(btor, idx, tp, *rest):
    if btor.is_bool_(tp):
        term = msat_make_true(btor.env)
    else:
        ok, w = msat_is_bv_type(btor.env, btor.get_type_(tp))
        assert ok
        term = msat_make_bv_number(btor.env, "1" * w, w, 2)
    btor.set(idx, term, tp)


def parse_array(btor, idx, ew, iw, *rest):
    btor.mk_array_var(idx, ew, iw)

    
def parse_array_read(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)
    term = msat_make_array_read(btor.env, t1, t2)
    btor.set(idx, term, w)


def parse_array_write(btor, idx, sort, a1, a2, a3, *rest):
    term = msat_make_array_write(btor.env, btor.get(a1, bvcontext),
                                 btor.get(a2, bvcontext),
                                 btor.get(a3, bvcontext))
    btor.set(idx, term, sort)


def parse_next(btor, idx, sort, v, e, *rest):
    btor.set_next(sort, v, e)


def parse_init(btor, idx, sort, v, e, *rest):
    btor.set_init(sort, v, e)


def parse_bv_ugt(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)
    t3 = msat_make_bv_uleq(btor.env, t1, t2)
    t4 = msat_make_not(btor.env, t3)
    btor.set(idx, t4, w)


def parse_bv_ugeq(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)
    t3 = msat_make_bv_ult(btor.env, t1, t2)
    t4 = msat_make_not(btor.env, t3)
    btor.set(idx, t4, w)


def parse_bv_sgt(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)
    t3 = msat_make_bv_sleq(btor.env, t1, t2)
    t4 = msat_make_not(btor.env, t3)
    btor.set(idx, t4, w)


def parse_bv_sgeq(btor, idx, w, a1, a2, *rest):
    t1 = btor.get(a1, bvcontext)
    t2 = btor.get(a2, bvcontext)
    t3 = msat_make_bv_slt(btor.env, t1, t2)
    t4 = msat_make_not(btor.env, t3)
    btor.set(idx, t4, w)


def parse_reduce_or(btor, idx, w, a, *rest):
    t1 = btor.get(a, bvcontext)
    ok, w1 = msat_is_bv_type(btor.env, msat_term_get_type(t1))
    assert ok
    t2 = msat_make_bv_number(btor.env, "1", w1, 10)
    t3 = msat_make_bv_ult(btor.env, t1, t2)
    t4 = msat_make_not(btor.env, t3)
    btor.set(idx, t4, w)


def parse_reduce_and(btor, idx, w, a, *rest):
    t1 = btor.get(a, bvcontext)
    ok, w1 = msat_is_bv_type(btor.env, msat_term_get_type(t1))
    assert ok
    t2 = msat_make_bv_number(btor.env, "0", w1, 10)
    t3 = msat_make_bv_not(btor.env, t1)
    t4 = msat_make_equal(btor.env, t3, t2)
    btor.set(idx, t4, w)


def parse_reduce_xor(btor, idx, w, a, *rest):
    t1 = btor.get(a, bvcontext)
    ok, w1 = msat_is_bv_type(btor.env, msat_term_get_type(t1))
    assert ok
    res = msat_make_bv_extract(btor.env, 0, 0, t1)
    for i in range(1, w1):
        b = msat_make_bv_extract(btor.env, i, i, t1)
        res = msat_make_bv_xor(btor.env, res, b)
    btor.set(idx, res, w)


def parse_ite(btor, idx, sort, c, t, e, *rest):
    ct = btor.get(c, boolcontext)
    if btor.is_bool_(sort):
        tt = btor.get(t, boolcontext)
        et = btor.get(e, boolcontext)
        term = msat_make_and(btor.env,
                             msat_make_or(btor.env,
                                          msat_make_not(btor.env, ct), tt),
                             msat_make_or(btor.env, ct, et))
    else:
        tt = btor.get(t, bvcontext)
        et = btor.get(e, bvcontext)
        term = msat_make_term_ite(btor.env, ct, tt, et)
    btor.set(idx, term, sort)


def parse_bad(btor, idx, bad, *rest):
    btor.add_bad(bad)


def parse_constraint(btor, idx, constr, *rest):
    btor.add_constraint(constr)


def parse_output(btor, idx, out, *rest):
    btor.add_output(out)


def parse_uext(btor, idx, sort, elem, amount, *rest):
    v = btor.get(elem, bvcontext)
    t = msat_make_bv_zext(btor.env, amount, v)
    btor.set(idx, t, sort)


def parse_sext(btor, idx, sort, elem, amount, *rest):
    v = btor.get(elem, bvcontext)
    t = msat_make_bv_sext(btor.env, amount, v)
    btor.set(idx, t, sort)


opmap = {
    "sort" : parse_sort,
    "input" : parse_input,
    "constd" : parse_bv_number(10),
    "consth" : parse_bv_number(16),
    "const" : parse_bv_number(2),
    "not" : parse_not,
    "and" : parse_bool_connective(msat_make_and, msat_make_bv_and),
    "or" : parse_bool_connective(msat_make_or, msat_make_bv_or),
    "xor" : parse_bool_connective(make_xor, msat_make_bv_xor),
    "xnor" : parse_bool_connective(make_xnor, make_bv_xnor),
    "neg" : parse_bv_neg,
    "implies" : parse_bool_connective(make_implies, make_bv_implies),
    "slice" : parse_bv_slice,
    "add" : parse_bv_op(msat_make_bv_plus),
    "mul" : parse_bv_op(msat_make_bv_times),
    "urem" : parse_bv_op(msat_make_bv_urem),
    "srem" : parse_bv_op(msat_make_bv_srem),
    "udiv" : parse_bv_op(msat_make_bv_udiv),
    "sdiv" : parse_bv_op(msat_make_bv_sdiv),
    "sub" : parse_bv_op(msat_make_bv_minus),
    "eq" : parse_equal,
    "neq" : parse_not_equal,
    "ult" : parse_bv_op(msat_make_bv_ult),
    "ulte" : parse_bv_op(msat_make_bv_uleq),
    "ugt" : parse_bv_ugt,
    "ugte" : parse_bv_ugeq,
    "sgt" : parse_bv_sgt,
    "sgte" : parse_bv_sgeq,
    "concat" : parse_bv_op(msat_make_bv_concat),
    "array" : parse_array,
    "read" : parse_array_read,
    "write" : parse_array_write,
    "sll" : parse_bv_shift(msat_make_bv_lshl),
    "srl" : parse_bv_shift(msat_make_bv_lshr),
    "sra" : parse_bv_shift(msat_make_bv_ashr),
    "slt" : parse_bv_op(msat_make_bv_slt),
    "next" : parse_next,
    "zero" : parse_zero,
    "one" : parse_one,
    "ones" : parse_ones,
    "redor" : parse_reduce_or,
    "redand" : parse_reduce_and,
    "redxor" : parse_reduce_xor,
    "init" : parse_init,
    "state" : parse_state,
    "ite" : parse_ite,
    "bad" : parse_bad,
    "uext" : parse_uext,
    "sext" : parse_sext,
    "output" : parse_output,
    "constraint" : parse_constraint,
    }


def toint(a):
    try:
        return int(a)
    except ValueError:
        return a


def warn(msg):
    sys.stderr.write('WARNING: %s\n' % msg)
    sys.stderr.flush()


def err(msg):
    sys.stderr.write('ERROR: %s\n' % msg)
    sys.stderr.flush()
    exit(1)


def is_input_constr(env, c, sv):
    res = [True]
    def visit(e, t, pre):
        if pre:
            if msat_term_is_constant(env, t):
                if t in sv:
                    res[0] = False
                    return MSAT_VISIT_ABORT
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, c, visit)
    return res[0]


def elim_inputs(env, constr, sv):
    def cheap_mb_elim(formula, toelim):
        wenv = msat_create_env({'bool_model_generation': 'true'}, env)
        msat_assert_formula(wenv, formula)
        res = msat_make_false(env)
        maxmodels = len(toelim) * 10
        for i in range(maxmodels):
            s = msat_solve(wenv)
            if s == MSAT_UNSAT:
                return res
            elif s == MSAT_SAT:
                values = []
                for v in toelim:
                    val = msat_get_model_value(wenv, v)
                    if MSAT_ERROR_TERM(val):
                        return None
                    if not msat_term_is_true(env, val) \
                           and not msat_term_is_false(env, val):
                        return None
                    else:
                        values.append(val)
                disj = msat_apply_substitution(wenv, formula, toelim, values)
                res = msat_make_or(wenv, res, disj)
                msat_assert_formula(wenv, msat_make_not(wenv, disj))
            else:
                break
        return None
    
    out = []
    def visit(e, t, pre):
        if pre:
            if msat_term_is_constant(env, t) \
                   and not msat_term_is_number(env, t):
                if t not in sv:
                    out.append(t)
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, constr, visit)

    tosubst = []
    removed = set()
    for v in out:
        if msat_is_bool_type(env, msat_term_get_type(v)):
            tosubst.append(v)
            removed.add(msat_decl_get_name(msat_term_get_decl(v)))
    if tosubst:
        res = cheap_mb_elim(constr, tosubst)
        if res is not None:
            constr = res
        else:
            removed = set()

    return constr, removed


def add_constraint(env, init, prop, constr, iconstr, removed):
    #return init, prop
    res = [False]
    def visit(e, t, pre):
        if pre and msat_term_is_constant(e, t):
            name = msat_decl_get_name(msat_term_get_decl(t))
            if name in removed:
                res[0] = True
                return MSAT_VISIT_ABORT
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, init, visit)
    msat_visit_term(env, prop, visit)
    cc = constr if res[0] else iconstr
    init = msat_make_and(env, init, cc)
    prop = msat_make_or(env, msat_make_not(env, cc), prop)
    return init, prop


def ensure_state_vars(env, init, prop, statevars):
    sv = set()
    for (c, n) in statevars:
        sv.add(msat_decl_get_name(msat_term_get_decl(c)))
        sv.add(msat_decl_get_name(msat_term_get_decl(n)))

    def visit(e, t, pre):
        if pre:
            if msat_term_is_constant(e, t):
                name = msat_decl_get_name(msat_term_get_decl(t))
                if name not in sv:
                    nn = name + ".next"
                    d = msat_find_decl(env, nn)
                    assert MSAT_ERROR_DECL(d)
                    d = msat_declare_function(env, nn, msat_term_get_type(t))
                    statevars.append((t, msat_make_constant(env, d)))
                    sv.add(name)
                    sv.add(nn)
        return MSAT_VISIT_PROCESS

    msat_visit_term(env, init, visit)
    msat_visit_term(env, prop, visit)

    return statevars


def main():
    env = msat_create_env({'preprocessor.simplification' : '7'})
    btor = BTORConverter(env)

    for i, line in enumerate(sys.stdin):
        i += 1
        try:
            line = line[:line.index(';')]
        except ValueError:
            pass
        line = line.strip()
        if not line:
            continue
        tokens = line.split()
        if len(tokens) < 2:
            print("malformed input at line %d: %s" % (i, line))
            raise Exception(line)
        try:
            op = tokens[1]
            func = opmap[op]
            args = [btor, int(tokens[0])] + [toint(t) for t in tokens[2:]]
            func(*args)
        except Exception:
            print("error at line %d: %s" % (i, line))
            raise

    if not btor.registers:
        btor.to_smt(sys.stdout)
    else:
        btor.to_vmt(sys.stdout)

    msat_destroy_env(env)


if __name__ == '__main__':
    main()
