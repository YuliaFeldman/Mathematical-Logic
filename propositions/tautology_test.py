# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology_test.py

"""Tests for the propositions.tautology module."""

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.tautology import *

from propositions.proofs_test import offending_line

def test_formulae_capturing_model(debug=False):
    for q,a in [({'p':True},['p']),
                ({'q7':False}, ['~q7']),
                ({'x1':True, 'x2':False, 'x3':True}, ['x1', '~x2', 'x3']),
                ({'q3':False, 'p13':False, 'r':True}, ['~p13', '~q3', 'r'])]:
        if debug:
            print("Testing formulae_capturing_model on", q)
        aa = [Formula.parse(f) for f in a]
        assert formulae_capturing_model(frozendict(q)) == aa


def test_prove_in_model(debug=False):
    for (f, m, a, cp) in [ ('x', {'x':True}, ['x'], ''),
                           ('x',{'x':False}, ['~x'], '~'),
                           ('~x', {'x':False}, ['~x'], ''),
                           ('~x', {'x':True}, ['x'], '~'),
                           ('x', {'x':True, 'z5':False}, ['x', '~z5'], ''),
                           ('(p->~p)', {'p':True}, ['p'], '~'),
                           ('(p->~p)', {'p':False}, ['~p'], ''),
                           ('(p->q)', {'p':True, 'q':True}, ['p','q'], ''),
                           ('(p->q)', {'p':True, 'q':False}, ['p','~q'], '~'),
                           ('(p->q)', {'p':False, 'q':True}, ['~p','q'], ''),
                           ('(p->q)', {'p':False, 'q':False}, ['~p', '~q'], ''),
                           ('~~~~y7', {'y7':True}, ['y7'], ''),
                           ('~~~~y7', {'y7':False}, ['~y7'], '~'),
                           ('~(~p->~q)', {'p':True, 'q':True}, ['p','q'], '~'),
                           ('~(~p->~q)', {'p':False, 'q':True}, ['~p','q'], ''),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':True, 'p3':True, 'p4':True},
                            ['p1','p2','p3','p4'], ''),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':True, 'p3':True, 'p4':False},
                            ['p1','p2','p3','~p4'], '~'),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':False, 'p3':True, 'p4':False},
                            ['p1','~p2','p3','~p4'], ''),
                           ('(~(~x->~~y)->(z->(~x->~~~z)))',
                            {'z':True, 'x':False, 'y':False},
                            ['~x','~y','z'], '~')
                           ]:
        c = Formula.parse(cp + f)
        f = Formula.parse(f)
        a = (Formula.parse(v) for v in a)
        if debug:
            print('testing prove_in_model on formula', f, 'in model', m)
        p = prove_in_model(f, frozendict(m))
        assert p.statement == InferenceRule(a,c)
        assert p.rules == AXIOMATIC_SYSTEM
        assert p.is_valid(), offending_line(p)


        
def test_reduce_assumption(debug=False):
    for f, m, v in [ ('(y->x)', {'x':True}, 'y'),
                     ('(p->p)', {}, 'p'),
                     ('(p->(r->q))', {'p':True, 'q':True}, 'r')]:
        f = Formula.parse(f)
        m[v]=True
        pt = prove_in_model(f, frozendict(m))
        m[v]=False
        pf = prove_in_model(f, frozendict(m))
        if debug:
            print("testing reduce assumption on", pt.statement, "and",
                  pf.statement)
        p = reduce_assumption(pt,pf)
        assert p.statement.conclusion  == pf.statement.conclusion
        assert p.statement.assumptions[:] == pt.statement.assumptions[:-1]
        assert p.rules == AXIOMATIC_SYSTEM
        assert p.is_valid(), offending_line(p)


def test_prove_tautology(debug=False):
    for f, m in [ ('(p->p)', {'p':True}),
                  ('(p->p)', {'p':False}),
                  ('(p->p)', {}),
                  ('((~q->~p)->(p->q))', {'p':True, 'q':False}),
                  ('((~q->~p)->(p->q))', {'p':False}),
                  ('((~q->~p)->(p->q))', {})
                  ]:
        f = Formula.parse(f)
        if debug:
            print("Testing prove_tautology on formula", f, "and model", m)
        p = prove_tautology(f, frozendict(m))
        assert p.statement.conclusion == f
        assert p.statement.assumptions == tuple(formulae_capturing_model(m))
        assert p.rules == AXIOMATIC_SYSTEM
        assert p.is_valid(), offending_line(p)


    for t in [ '((~q->~p)->(p->q))', '(~~p->p)', '(p->~~p)',
               '((~p->~q)->((p->~q)->~q))',
               #'((p1->(p2->(p3->p4)))->(p3->(p2->(p1->p4))))',  
               '((p2->(p3->p4))->(p3->(p2->p4)))',
               #'(((((p->q)->(~r->~s))->r)->t)->((t->p)->(s->p)))',   
               #'(((((r->q)->(~r->~q))->r)->t)->((t->r)->(q->r)))',    
               '(~~~~x13->~~x13)']:
        t = Formula.parse(t)
        if debug:
            print("Testing prove_tautology on formula", t)
        p = prove_tautology(t)
        if debug:
            if len(p.lines)<20:
                print("Proof is",p)
            else:
                print("Proof has", len(p.lines), "lines.")
        assert len(p.statement.assumptions) == 0
        assert p.statement.conclusion == t
        assert p.rules == AXIOMATIC_SYSTEM
        assert p.is_valid(), offending_line(p)


def test_proof_or_counterexample(debug=False):
    for f in [ 'x', '(y->y)', '((x->y)->(x->y))', '((x->y)->z)',
               '((~p->~q)->((p->~q)->~q))', '((~p->~r)->((p->~q)->~q))',
               '((~p->~q)->((~p->q)->p))', '((q->~p)->((~~~p->r)->(q->r)))',
               '((q->p)->((~q->p)->p))', '((p->~q)->(q->~p))',
               '((p->q)->(~p->~q))']:
        if debug:
            print("Testing proof_or_counterexample on", f)
        f = Formula.parse(f)
        p = proof_or_counterexample(f)
        if type(p) is Proof:
            assert len(p.statement.assumptions) == 0
            assert p.statement.conclusion == f
            assert p.rules == AXIOMATIC_SYSTEM
            assert p.is_valid(), offending_line(p)
        else:
            assert not evaluate(f,p)

def test_encode_as_formula(debug=False):
        for r,f in [(InferenceRule([Formula.parse('x')],
                                   Formula.parse('y')), '(x->y)'),
                    (InferenceRule([Formula.parse('x'), Formula.parse('y')],
                                   Formula.parse('z')), '(x->(y->z))'),
                    (InferenceRule([Formula.parse('~y'),
                                    Formula.parse('(x->y)')],
                                   Formula.parse('~x')), '(~y->((x->y)->~x))'),
                    (InferenceRule([Formula.parse('~p'),
                                    Formula.parse('(q->p)'),
                                    Formula.parse('z')], Formula.parse('~q')),
                     '(~p->((q->p)->(z->~q)))')]:
            f = Formula.parse(f)
            if debug:
                print("Testing encode_as_formula on:", r)
            ff = encode_as_formula(r)
            assert f == ff

def test_prove_sound_inference(debug=False):
    for a,c in [ ([], '(p->p)'),
                 (['p'], 'p'),
                 (['p'], '~~p'),
                 (['~~p'], 'p'),
                 (['p'], '(q->p)'),
                 (['(p->q)'], '(~q->~p)'),
                 (['p', 'q'], '~(p->~q)'),
                 (['(p->q)', '(q->r)'], '(p->r)'),
                 #(['p','(p->q)', '(q->r)', '~r'],'x'),
                 (['p', '~p'], 'q')
                 ]:
        r = InferenceRule((Formula.parse(f) for f in a), Formula.parse(c))
        if debug:
            print("Testing prove_sound_inference on", r)
        p = prove_sound_inference(r)
        assert p.statement == r
        assert p.rules == AXIOMATIC_SYSTEM
        assert p.is_valid(), offending_line(p)


def test_model_or_inconsistency(debug=False):
    for s in [ {'p'}, {'p','~p'}, {'(p->p)'}, {'~(p->p)'},
               {'(x->y)', 'x', '~y'}, {'(x->y)', 'x', '~z'}]:
        s = { Formula.parse(f) for f in s }
        if debug:
            print("Testing model_or_inconsistency on", s)
        r = model_or_inconsistency(s)
        if type(r) is Proof:
            assert r.statement.conclusion == Formula.parse('~(p->p)')
            assert set(r.statement.assumptions) == s
            assert r.rules == AXIOMATIC_SYSTEM
            assert r.is_valid(), offending_line(r)
        else:
            assert is_model(r)
            for f in s:
                assert evaluate(f,r)

def test_prove_in_model_full(debug=False):
    for (f, m, a, cp) in [ ('x', {'x':True}, ['x'], ''),
                           ('x',{'x':False}, ['~x'], '~'),
                           ('~x', {'x':False}, ['~x'], ''),
                           ('~x', {'x':True}, ['x'], '~'),
                           ('x', {'x':True, 'z5':False}, ['x', '~z5'], ''),
                           ('(p->~p)', {'p':True}, ['p'], '~'),
                           ('(p->~p)', {'p':False}, ['~p'], ''),
                           ('(p->q)', {'p':True, 'q':True}, ['p','q'], ''),
                           ('(p->q)', {'p':True, 'q':False}, ['p','~q'], '~'),
                           ('(p->q)', {'p':False, 'q':True}, ['~p','q'], ''),
                           ('(p->q)', {'p':False, 'q':False}, ['~p', '~q'], ''),
                           ('~~~~y7', {'y7':True}, ['y7'], ''),
                           ('~~~~y7', {'y7':False}, ['~y7'], '~'),
                           ('~(~p->~q)', {'p':True, 'q':True}, ['p','q'], '~'),
                           ('~(~p->~q)', {'p':False, 'q':True}, ['~p','q'], ''),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':True, 'p3':True, 'p4':True},
                            ['p1','p2','p3','p4'], ''),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':True, 'p3':True, 'p4':False},
                            ['p1','p2','p3','~p4'], '~'),
                           ('((p1->p2)->(p3->p4))',
                            {'p1':True, 'p2':False, 'p3':True, 'p4':False},
                            ['p1','~p2','p3','~p4'], ''),
                           ('(~(~x->~~y)->(z->(~x->~~~z)))',
                            {'z':True, 'x':False, 'y':False},
                            ['~x','~y','z'], '~'),
                           ('T', {}, [], ''),
                           ('F', {}, [], '~'),
                           ('(p|q)', {'p': True, 'q': True}, ['p', 'q'], ''),
                           ('(p|q)', {'p': True, 'q': False}, ['p', '~q'], ''),
                           ('(p|q)', {'p': False, 'q': True}, ['~p', 'q'], ''),
                           ('(p|q)',
                            {'p': False, 'q': False}, ['~p', '~q'], '~'),
                           ('(p&q)', {'p': True, 'q': True}, ['p', 'q'], ''),
                           ('(p&q)', {'p': True, 'q': False}, ['p', '~q'], '~'),
                           ('(p&q)', {'p': False, 'q': True}, ['~p', 'q'], '~'),
                           ('(p&q)',
                            {'p': False, 'q': False}, ['~p', '~q'], '~'),
                           ('~(~(q|p)&(r->~(s|q)))',
                            {'p': False, 'q': False, 'r': False, 's': False},
                            ['~p', '~q', '~r', '~s'], '~'),
                           ('~(~(q|p)&(r->~(s|q)))',
                            {'p': False, 'q': False, 'r': True, 's': True},
                            ['~p', '~q', 'r', 's'], '')
                           ]:
        c = Formula.parse(cp+f)
        f = Formula.parse(f)
        a = (Formula.parse(v) for v in a)
        if debug:
            print('Testing prove_in_model_full on formula',f, 'in model', m)
        p = prove_in_model_full(f, frozendict(m))
        assert p.statement == InferenceRule(a, c)
        assert p.rules == AXIOMATIC_SYSTEM_FULL
        assert p.is_valid(), offending_line(p)
           
def test_ex6(debug=False):
    test_formulae_capturing_model(debug)
    test_prove_in_model(debug)
    test_reduce_assumption(debug)
    test_prove_tautology(debug)
    test_proof_or_counterexample(debug)
    test_encode_as_formula(debug)
    test_prove_sound_inference(debug)
    test_model_or_inconsistency(debug)

def test_ex6_opt(debug=False):
    test_prove_in_model_full(debug)

def test_all(debug=False):
    test_ex6(debug)
    test_ex6_opt(debug)
