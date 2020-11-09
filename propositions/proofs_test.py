# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs_test.py

"""Tests for the propositions.proofs module."""

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *

# Tests for InferenceRule

def test_variables(debug=False):
    for assumptions, conclusion, variables in [
            [[], 'T', set()],
            [['p', 'q'], 'r', {'p', 'q', 'r'}],
            [['(p|q)', '(q|r)', '(r|p)'], '(p->(q&s))', {'p', 'q', 'r', 's'}],
            [['(x1&x2)', '(x3|x4)'], '(x1->x11)',
             {'x1', 'x2', 'x3', 'x4', 'x11'}],
            [['~z', '~y', '~x'], '(((x|y)|z)|w)', {'z', 'y', 'x', 'w'}],
            [['~~z'], '((~~z->z)|z)', {'z'}]]:
        rule = InferenceRule([Formula.parse(a) for a in assumptions],
                             Formula.parse(conclusion))
        if debug:
            print('Testing variables of the inference rule', rule)
        assert rule.variables() == variables

substitutions = [
    [ {},
      ['p', 'p'],
      ['(p->q)','(p->q)'],
      ['~x','~x'],
      ['T','T']],
    [ {'p':'p1'},
      ['p', 'p1'],
      ['(p->q)','(p1->q)'],
      ['~p1','~p1'],
      ['T','T'],
      ['(p&p)','(p1&p1)'],
      ['(p->p1)', '(p1->p1)']],
    [ {'p':'(x|y)'},
      ['p', '(x|y)'],
      ['(p->q)','((x|y)->q)'],
      ['~p','~(x|y)'],
      ['(T&~p)','(T&~(x|y))'],
      ['(p&p)','((x|y)&(x|y))']],
    [ {'p':'(x|y)', 'q':'~w'},
      ['p', '(x|y)'],
      ['q', '~w'],
      ['z', 'z'],
      ['w', 'w'],
      ['(p->q)','((x|y)->~w)'],
      ['~p','~(x|y)'],
      ['(T&~p)','(T&~(x|y))'],
      ['(p&p)','((x|y)&(x|y))'],
      ['((p->q)->(~q->~p))', '(((x|y)->~w)->(~~w->~(x|y)))']],
    [ {'x':'F', 'y':'~T', 'z':'p'},
      ['x','F'],
      ['((x&x)->y)', '((F&F)->~T)'],
      ['~(z|x)', '~(p|F)'],
      ['((z|x)&~(x->y))','((p|F)&~(F->~T))']]
    ]

def test_specialize(debug=False):
    for t in substitutions:
        d = t[0]
        if debug:
            print('Testing substitition dictionary', d)
        d = frozendict({k: Formula.parse(d[k]) for k in d})
        cases = [ [Formula.parse(c[0]), Formula.parse(c[1])] for c in t[1:]]
        for case in cases:
            if debug:
                print('...checking that', case[0], 'specializes to', case[1])
            general = InferenceRule([],case[0])
            special = InferenceRule([],case[1])
            assert general.specialize(d) == special, \
                   "got " + str(general.specialize(d).conclusion)
        if debug:
            print('...now checking all together in a single rule')
            general = InferenceRule([case[0] for case in cases[1:]],cases[0][0])
            special = InferenceRule([case[1] for case in cases[1:]],cases[0][1])
            assert general.specialize(d) == special, \
                   "got " + str(general.specialize(d))      

def test_merge_specialization_maps(debug=False):
    for d1, d2, d in [
        ({}, {}, {}),
        ({}, None, None),
        (None, {}, None),
        (None, None, None),
        ({'p':'q'}, {'r':'s'}, {'p':'q', 'r':'s'}),
        ({'p':'q'}, {}, {'p':'q'}),
        ({}, {'p':'q'}, {'p':'q'}),
        ({'p':'q'}, {'p':'r'}, None),
        ({'p':'q'}, None, None),
        (None, {'p':'q'}, None),
        ({'x':'p1', 'y':'p2'}, {'x':'p1', 'z':'p3'},
         {'x':'p1', 'y':'p2', 'z':'p3'}),
        ({'x':'p1', 'y':'p2'}, {'x':'p1', 'y':'p3'}, None),
        ({'x':'p1', 'y':'p2'}, {'x':'p1', 'y':'p2', 'z':'p3'},
         {'x':'p1', 'y':'p2', 'z':'p3'}),
        ({'x':'p1', 'y':'p2', 'z':'p3'}, {'x':'p1', 'y':'p2'},
         {'x':'p1', 'y':'p2', 'z':'p3'})]:
        if debug:
            print('Testing merging of dictionaries', d1, d2)
        dd = InferenceRule.merge_specialization_maps(
            frozendict({v: Formula.parse(d1[v]) for v in d1}) if d1 is not None
            else None,
            frozendict({v: Formula.parse(d2[v]) for v in d2}) if d2 is not None
            else None)
        assert dd == ({v: Formula.parse(d[v]) for v in d}
                      if d is not None else None), "got " + dd

specializations = [
      ['p', 'p', {'p':'p'}],
      ['(p->q)','(p->q)', {'p':'p', 'q':'q'}],
      ['~x','~x', {'x':'x'}],
      ['p', 'p1', {'p':'p1'}],
      ['(p->q)','(p1->q)', {'p':'p1', 'q':'q'}],
      ['~p1','~p1',{'p1':'p1'}],
      ['(p&p)','(p1&p1)', {'p':'p1'}],
      ['(p->p1)', '(p1->p1)', {'p':'p1', 'p1':'p1'}],
      ['p', '(x|y)', {'p':'(x|y)'}],
      ['(p->q)','((x|y)->q)', {'p':'(x|y)', 'q':'q'}],
      ['~p','~(x|y)', {'p':'(x|y)'}],
      ['(T&~p)','(T&~(x|y))', {'p':'(x|y)'}],
      ['(p&p)','((x|y)&(x|y))', {'p':'(x|y)'}],
      ['(p->q)','((x|y)->~w)', {'p':'(x|y)', 'q':'~w'}],
      ['((p->q)->(~q->~p))', '(((x|y)->~w)->(~~w->~(x|y)))',
       {'p':'(x|y)', 'q':'~w'}],
      ['((x|x)&x)','((F|F)&F)', {'x':'F'}],
      ['x','T', {'x':'T'}],
      ['y','(x&~(y->z))', {'y':'(x&~(y->z))'}],
      ['T', 'T', {}],
      ['(F&T)','(F&T)',{}],
      ['F','x',None],
      ['~F', 'x', None],
      ['~F', '~x', None],
      ['~F', '~T', None],
      ['F', '(x|y)', None],
      ['(x&y)', 'F', None],
      ['(x&y)', '(F&F)', {'x':'F', 'y':'F'}],
      ['(x&y)', '(F&~T)', {'x':'F', 'y':'~T'}],      
      ['(x&x)', '(F&T)', None],
      ['(F&F)', '(x&y)',  None],
      ['(F&T)', '(F|T)', None],
      ['~F', '(F|T)', None],
      ['((x&y)->x)', '((F&F)->T)', None],
      ['((x&y)->x)', '((F&F)|F)', None],
      ['(~p->~(q|T))', '(~(x|y)->~((z&(w->~z))|T))',
       {'p':'(x|y)', 'q':'(z&(w->~z))'}],
      ['(~p->~(q|T))', '(~(x|y)->((z&(w->~z))|T))', None],
      ['(~p->~(q|T))', '(~(x|y)->~((z&(w->~z))|F))', None]
    ]
 
def test_formula_specialization_map(debug=False):
    for t in specializations:
        g = Formula.parse(t[0])
        s = Formula.parse(t[1])
        d = None if t[2] == None else {k: Formula.parse(t[2][k]) for k in t[2]}
        if debug:
            print("Checking if and how formula ",s,"is a special case of",g)
        dd = InferenceRule.formula_specialization_map(g,s)
        if dd != None:
            for k in dd:
                assert is_variable(k)
                assert type(dd[k]) is Formula
        assert dd == d, "expected " + str(d) + " got " + str(dd)

rules = [
    ['(~p->~(q|T))', '(~(x|y)->~((z&(w->~z))|T))', [], [],
     {'p':'(x|y)', 'q':'(z&(w->~z))'}],
    ['(~p->~(q|T))', '(~(x|y)->((z&(w->~z))|T))', [], [], None],
    ['T', 'T', ['(~p->~(q|T))'], ['(~(x|y)->~((z&(w->~z))|T))'],
     {'p':'(x|y)', 'q':'(z&(w->~z))'}],
    ['F', 'F', ['(~p->~(q|T))'], ['(~(x|y)->((z&(w->~z))|T))'], None],
    ['p', 'p', ['(p->q)'],['(p->q)'], {'p':'p', 'q':'q'}],
    ['p', 'p', ['(p->q)'],['(p->q)', '(p->q)'], None],
    ['p', 'p', ['(p->q)', '(p->q)'],['(p->q)'], None],
    ['p', 'p', ['(p->q)','(p->q)'],['(p->q)','(p->q)'], {'p':'p', 'q':'q'}],    
    ['p', 'r', ['(p->q)'],['(r->q)'], {'p':'r', 'q':'q'}],    
    ['p', 'r', ['(p->q)'],['(z->q)'], None],
    ['p', 'p1', ['(p->q)', '(p&p)'], ['(p1->r)','(p1&p1)'],
     {'p':'p1', 'q':'r'}],
    ['p', 'p1', ['(p->q)', '(p&p)'], ['(p1->(r&~z))','(p1&p1)'],
     {'p':'p1', 'q':'(r&~z)'}],
    ['p', '~T', ['(p->q)', '(p&p)'], ['(~T->(r&~z))','(~T&~T)'],
     {'p':'~T', 'q':'(r&~z)'}],
    ['p', 'T', ['(p->q)', '(p&p)'], ['(~T->(r&~z))','(~T&~T)'], None],
    ['p', '~T', ['(p->q)', '(p&p)'], ['(~T->(r&~z))','(~F&~F)'], None]
]
     
def test_specialization_map(debug=False):
    for t in rules:
        g = InferenceRule([Formula.parse(f) for f in t[2]], Formula.parse(t[0]))
        s = InferenceRule([Formula.parse(f) for f in t[3]], Formula.parse(t[1]))
        d = None if t[4] is None else {v: Formula.parse(t[4][v]) for v in t[4]}
        if debug:
            print("Testing if and how rule ", s, "is a special case of", g)
        dd = g.specialization_map(s)
        assert d == dd, "expected " + str(d) + " got " + str(dd)
   
def test_is_specialization_of(debug=False):
    # Test 1
    rule = InferenceRule([], Formula.parse('(~p|p)'))
    for conclusion, instantiation_map_infix in [
            ['(~q|q)', {'p': 'q'}],
            ['(~p|p)', {'p': 'p'}],
            ['(~p4|p4)', {'p': 'p4'}],
            ['(~r7|r7)', {'p': 'r7'}],
            ['(~~(p|q)|~(p|q))', {'p': '~(p|q)'}],
            ['(~p|q)', None],
            ['(~p1|p2)', None],
            ['(~~(p|p)|~(p|q))', None]]:
        candidate = InferenceRule([], Formula.parse(conclusion))
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == \
               (instantiation_map_infix is not None)

    # Test 2
    rule = InferenceRule(
        [], Formula.parse('~(x|((p->(q&x))|((p|y)->(r&q))))'))
    for conclusion, value in [
            ['~(y|((p->((q->x)&y))|((p|x)->((r|q)&(q->x)))))', True],
            ['~(y|((p->((q->x)|y))|((p|x1)->((r|q)&(q->x)))))', False]]:
        candidate = InferenceRule([], Formula.parse(conclusion))
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == value

    # Test 3
    a = Formula.parse('(~p|q)')
    b = Formula.parse('p')
    c = Formula.parse('q')
    aa = Formula.parse('(~x|y)')
    bb = Formula.parse('x')
    cc = Formula.parse('y')
    rule = InferenceRule([a, b], c)
    for assumptions, conclusion, value in [[[aa, bb], cc, True],
                                           [[aa, bb], c, False],
                                           [[aa, b], cc, False],
                                           [[a, bb], cc, False]]:
        candidate = InferenceRule(assumptions, conclusion)
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == value
            
    # Test 4
    a = Formula.parse('(p|q)')
    b = Formula.parse('(~p|r)')
    c = Formula.parse('(q|r)')
    aa = Formula.parse('((x1&x2)|((p|q)|r))')
    bb = Formula.parse('(~(x1&x2)|~y)')
    cc = Formula.parse('(((p|q)|r)|~y)')
    rule = InferenceRule([a, b], c)
    instantiation_map = {'p': Formula.parse('(x1&x2)'),
                         'q': Formula.parse('((p|q)|r)'),
                         'r': Formula.parse('~y')}
    for assumptions, conclusion, value in [
            [[aa, bb], cc, True],
            [[aa, bb], Formula.parse('(((p|q)|r)|r)'), False],
            [[aa, bb], c, False],
            [[aa, b], cc, False],
            [[a, bb], cc, False]]:
        candidate = InferenceRule(assumptions, conclusion)
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == value

    # Test 5
    a = Formula.parse('((x->y)->x)')
    b = Formula.parse('((y->x)->y)')
    c = Formula.parse('y')
    aa = Formula.parse('((~x->x)->~x)')
    bb = Formula.parse('((x->~x)->x)')
    cc = Formula.parse('x')
    rule = InferenceRule([a, b], c)
    for assumptions, conclusion, value in [[[aa, bb], cc, True],
                                           [[bb, aa], cc, False],
                                           [[a, bb], cc, False],
                                           [[aa, b], cc, False],
                                           [[aa, bb], c, False]]:
        candidate = InferenceRule(assumptions, conclusion)
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == value

    # Test 6
    a = Formula.parse('(((p&q)&p)&p)')
    b = Formula.parse('(((q&p)&q)&q)')
    c = Formula.parse('(p->q)')
    aa = Formula.parse('((((p->F)&~p)&(p->F))&(p->F))')
    bb = Formula.parse('(((~p&(p->F))&~p)&~p)')
    cc = Formula.parse('((p->F)->~p)')
    rule = InferenceRule([a, b], c)
    for assumptions, conclusion, value in [[[aa, bb], cc, True],
                                           [[bb, aa], cc, False],
                                           [[a, bb], cc, False],
                                           [[aa, b], cc, False],
                                           [[aa, bb], c, False]]:
        candidate = InferenceRule(assumptions, conclusion)
        if debug:
            print('Testing whether', candidate, 'is a special case of', rule)
        assert candidate.is_specialization_of(rule) == value

# Two proofs for use in various tests below

R1 = InferenceRule([Formula.parse('(p|q)'), Formula.parse('(~p|r)')],
                   Formula.parse('(q|r)'))
R2 = InferenceRule([], Formula.parse('(~p|p)'))
DISJUNCTION_COMMUTATIVITY_PROOF = Proof(
    InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)')),
    {R1, R2},
    [Proof.Line(Formula.parse('(x|y)')),
     Proof.Line(Formula.parse('(~x|x)'), R2, []),
     Proof.Line(Formula.parse('(y|x)'), R1, [0, 1])])

R3 = InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)'))
R4 = InferenceRule([Formula.parse('(x|(y|z))')],
                   Formula.parse('((x|y)|z)'))
DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF = Proof(
    InferenceRule([Formula.parse('((x|y)|z)')],
                  Formula.parse('(x|(y|z))')),
    {R3, R4},
    [Proof.Line(Formula.parse('((x|y)|z)')),
     Proof.Line(Formula.parse('(z|(x|y))'), R3, [0]),
     Proof.Line(Formula.parse('((z|x)|y)'), R4, [1]),
     Proof.Line(Formula.parse('(y|(z|x))'), R3, [2]),
     Proof.Line(Formula.parse('((y|z)|x)'), R4, [3]),
     Proof.Line(Formula.parse('(x|(y|z))'), R3, [4])])

# Tests for Proof

def test_rule_for_line(debug=False):
    x1 = Formula.parse('(x&y)')
    x2 = Formula.parse('(p12->p13)')
    x3 = Formula.parse('~~~~x')
    xyxy = Formula.parse('((x|y)->(x|y))')
    r1 = Formula.parse('r')
    lemma = InferenceRule([x1,x3], r1)
    p1 = Formula.parse('p')
    p2 = Formula.parse('~~p')
    p3 = Formula.parse('~~~~p')
    pp = Formula.parse('(p->p)')
    rule0 = InferenceRule([p2],p1)
    rule1 = InferenceRule([p1, p2],p3)
    rule2 = InferenceRule([],pp)
    z = [None]*6
    z[0] = (Proof.Line(x1), None)
    z[1] = (Proof.Line(x1, rule0, [0]),
            InferenceRule([x1],x1))
    z[2] = (Proof.Line(x2, rule0, [0]),
            InferenceRule([x1],x2))
    z[3] = (Proof.Line(x3, rule1, [2,1]),
            InferenceRule([x2,x1],x3))
    z[4] = (Proof.Line(p3, rule1, [2,1]),
            InferenceRule([x2,x1],p3))
    z[5] = (Proof.Line(xyxy, rule2, []),
            InferenceRule([], xyxy))
    proof = Proof(lemma, {rule0, rule1, rule2}, [r for (r,a) in z])
    if debug:
        print("\nChecking rule_for_line...")
    for i in range(len(z)):
        if debug:
            print("Checking rule of line", i, ":", proof.lines[i])
        assert proof.rule_for_line(i) == z[i][1]


def test_is_line_valid(debug=False):
    x1 = Formula.parse('x')
    x2 = Formula.parse('~~x')
    x3 = Formula.parse('~~~~x')
    ff = Formula.parse('(F->F)')
    r1 = Formula.parse('r')
    lemma = InferenceRule([x1,x3], r1)
    p1 = Formula.parse('p')
    p2 = Formula.parse('~~p')
    p3 = Formula.parse('~~~~p')
    pp = Formula.parse('(p->p)')
    rule0 = InferenceRule([p2],p1)
    rule1 = InferenceRule([p1, p2],p3)
    rule2 = InferenceRule([],pp)
    rule3 = InferenceRule([p1],p1)
    rule4 = InferenceRule([p1],p2)
    z = [None]*18
    z[0] = (Proof.Line(x1), True)
    z[1] = (Proof.Line(p1), False)
    z[2] = (Proof.Line(x2), False)
    z[3] = (Proof.Line(x1, rule0, [2]),True)
    z[4] = (Proof.Line(p1, rule0, [2]), False)
    z[5] = (Proof.Line(x3, rule1, [2]), False)
    z[6] = (Proof.Line(x2, InferenceRule([p2],Formula.parse('p')), [5]), True)
    z[7] = (Proof.Line(x2, rule0, [8]), False)    
    z[8] = (Proof.Line(x3, rule1, [0,6]), True)   
    z[9] = (Proof.Line(x3, rule1, [4,6]), False)
    z[10] = (Proof.Line(x3, InferenceRule([],x3), []), False)
    z[11] = (Proof.Line(ff, rule2, []), True)
    z[12] = (Proof.Line(ff, rule0, []), False)
    z[13] = (Proof.Line(p3, rule2, []), False)
    z[14] = (Proof.Line(ff, rule2, [12]), False)
    z[15] = (Proof.Line(x1, rule3, [0]), True)
    z[16] = (Proof.Line(x1, rule3, [16]), False)
    z[17] = (Proof.Line(x2, rule4, [15]), False)
    proof = Proof(lemma, {rule0, rule1, rule2, rule3}, [r for (r,a) in z])
    if debug:
        print("\nChecking proof line vailidity in proof of", lemma,
              "using rules", {rule0, rule1})
    for i in range(len(z)):
        if debug:
            print("Checking line", i, ":", proof.lines[i])
        assert proof.is_line_valid(i) == z[i][1]


def test_is_valid(debug=False):
    # Test variations on DISJUNCTION_COMMUTATIVITY_PROOF

    proof = DISJUNCTION_COMMUTATIVITY_PROOF
    if debug:
        print('\nTesting validity of the following deductive proof:\n' +
              str(proof))
    assert proof.is_valid()

    proof = Proof(InferenceRule([Formula.parse('p'), Formula.parse('(x|y)')],
                                Formula.parse('(y|x)')),
                  DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                  DISJUNCTION_COMMUTATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert proof.is_valid()

    proof = Proof(DISJUNCTION_COMMUTATIVITY_PROOF.statement,
                  DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                  [Proof.Line(Formula.parse('(~x|x)'), R2, []),
                   Proof.Line(Formula.parse('(x|y)')),
                   Proof.Line(Formula.parse('(y|x)'), R1, [1, 0])])
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert proof.is_valid()


    proof = Proof(DISJUNCTION_COMMUTATIVITY_PROOF.statement,
                  set(),
                  DISJUNCTION_COMMUTATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    proof = Proof(InferenceRule([Formula.parse('(x|y)')],
                                Formula.parse('(x|y)')),
                  DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                  DISJUNCTION_COMMUTATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    proof = Proof(DISJUNCTION_COMMUTATIVITY_PROOF.statement,
                  {R1, InferenceRule([], Formula.parse('(~x|~x)'))},
                  DISJUNCTION_COMMUTATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    proof = Proof(DISJUNCTION_COMMUTATIVITY_PROOF.statement,
                  DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                  [Proof.Line(Formula.parse('(x|y)')),
                   Proof.Line(Formula.parse('(y|x)'), R1, [0, 0])])
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    # Test variations on DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF

    proof = DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert proof.is_valid()

    proof = Proof(InferenceRule([Formula.parse('(x|y)')],
                                Formula.parse('(y|x)')),
                  DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.rules,
                  DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    proof = Proof(DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.statement,
                  {R3, InferenceRule([], Formula('F'))},
                  DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.lines)
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    proof = Proof(DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.statement,
                  DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.rules,
                  [Proof.Line(Formula.parse('((x|y)|z)')),
                   Proof.Line(Formula.parse('(x|(y|z))'), R3, [0])])
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

    # Test circular proof

    R0 = InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)'))
    proof = Proof(InferenceRule([], Formula.parse('(x|y)')),
        {InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)'))},
        [Proof.Line(Formula.parse('(y|x)'), R0, [1]),
         Proof.Line(Formula.parse('(x|y)'), R0, [0])])
    if debug:
        print('Testing validity of the following deductive proof:\n' +
              str(proof))
    assert not proof.is_valid()

# Tests for Chapter 5 tasks

def offending_line(proof):
    """Finds the first invalid line in the given proof.

    Parameters:
        proof: proof to search.

    Returns:
        An error message containing the line number and string representation of
        the first invalid line in the given proof, or ``None`` if all the lines
        of the given proof are valid."""
    for i in range(len(proof.lines)):
        if not proof.is_line_valid(i):
            return "Invalid Line " + str(i) + ": " + str(proof.lines[i])
    return None

def test_prove_specialization(debug=False):
    # Test instantiations of DISJUNCTION_COMMUTATIVITY_PROOF

    for instance_infix in [['(w|z)', '(z|w)'],
                           ['(p|q)', '(q|p)'],
                           ['(q|x)', '(x|q)'],
                           ['((p|y)|(~r|y))', '((~r|y)|(p|y))']]:
        instance = InferenceRule([Formula.parse(instance_infix[0])],
                                 Formula.parse(instance_infix[1]))
        if debug:
            print('Testing proof of special case for the instance',
                  str(instance) + '\nand the following proof:\n' +
                  str(DISJUNCTION_COMMUTATIVITY_PROOF))
        instance_proof = prove_specialization(
            DISJUNCTION_COMMUTATIVITY_PROOF, instance)
        #if debug:
            #print('Got:\n', instance_proof)
        assert instance_proof.statement == instance
        assert instance_proof.rules == DISJUNCTION_COMMUTATIVITY_PROOF.rules
        assert instance_proof.is_valid(), offending_line(instance_proof)

    # Test instantiations of DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF
    for instance_infix in [
                           ['((x|y)|z)', '(x|(y|z))'],
                            ['((p|q)|r)', '(p|(q|r))']
                           , ['((x|x)|x)', '(x|(x|x))']
                           , ['((~x|x)|(x|~x))', '(~x|(x|(x|~x)))']
                           , ['(((p->p)|(p|p))|(p&p))', '((p->p)|((p|p)|(p&p)))']
                           ]:
        instance = InferenceRule([Formula.parse(instance_infix[0])],
                                 Formula.parse(instance_infix[1]))
        if debug:
            print('Testing proof of special case for the instance',
                  str(instance) + '\nand the following proof:\n' +
                  str(DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF))
        instance_proof = prove_specialization(
            DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF, instance)
        #if debug:
            #print('Got:\n', instance_proof)
        assert instance_proof.statement == instance
        assert instance_proof.rules == \
               DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.rules
        assert instance_proof.is_valid(), offending_line(instance_proof)
        #print("___________________________________________________________")
        #print(instance_proof.statement)
        #print(instance_proof.rules)
        #for i in range(len(instance_proof.lines)):
        #    print(instance_proof.lines[i])
            #print(instance_proof.is_line_valid(i))
        #print(instance_proof.is_valid())
        #print(offending_line(instance_proof))
        #print("___________________________________________________________")
        #print(instance)
        #print(DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF.rules)


def test_inline_proof_once(debug=False):
    from propositions.some_proofs import prove_and_commutativity

    rule0 = InferenceRule([Formula.parse('((x|y)|z)')],
                          Formula.parse('(x|(y|z))'))
    # Disjunction commutativity with an unused assumption
    rule1 = InferenceRule([Formula.parse('(~q|q)'), Formula.parse('(x|y)')],
                          Formula.parse('(y|x)'))
    rule2 = InferenceRule([], Formula.parse('(~p|p)'))

    lemma1_proof = Proof(rule1,
                         DISJUNCTION_COMMUTATIVITY_PROOF.rules,
                         [Proof.Line(Formula.parse('(~x|x)'), R2, []),
                          Proof.Line(Formula.parse('(x|y)')),
                          Proof.Line(Formula.parse('(y|x)'), R1, [1, 0])])
    lemma2_proof = DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF
    assert lemma1_proof.is_valid(), offending_line(lemma1_proof)
    assert lemma2_proof.is_valid(), offending_line(lemma2_proof)

    # A proof that uses both disjunction commutativity (lemma 1) and
    # disjunction right associativity (lemma2), whose proof in turn also uses
    # disjunction commutativity (lemma 1).
    proof = Proof(
        InferenceRule([Formula.parse('((p|q)|r)')],
                      Formula.parse('((r|p)|q)')),
        {rule0, rule1, rule2},
        [Proof.Line(Formula.parse('((p|q)|r)')),
         Proof.Line(Formula.parse('(p|(q|r))'), rule0, [0]),
         Proof.Line(Formula.parse('(~q|q)'), rule2, []),
         Proof.Line(Formula.parse('((q|r)|p)'), rule1, [2, 1]),
         Proof.Line(Formula.parse('(q|(r|p))'), rule0, [3]),
         Proof.Line(Formula.parse('((r|p)|q)'), rule1, [2, 4])])

    # Test inlining lemma2_proof once into proof
    assert proof.is_valid(), offending_line(proof)
    rule = lemma2_proof.statement
    line_number = first_use_of_rule(proof, rule)
    if debug:
        print('Testing inline_proof_once (test 1). In main proof:\n',
              proof, "Replacing line", line_number,
              'with the proof of following lemma proof:\n',
              str(lemma2_proof))
    inlined_proof = inline_proof_once(proof, line_number, lemma2_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == proof.rules.union(lemma2_proof.rules)
    newuse = uses_of_rule(inlined_proof, rule)
    olduse = uses_of_rule(proof, rule)
    assert newuse == olduse - 1, \
        "Uses of rule went from " + str(olduse) + " to " + str(newuse)
    assert inlined_proof.is_valid(), offending_line(inlined_proof)

    # Test inlining lemma2_proof into result of previous inlining
    proof = inlined_proof
    assert proof.is_valid(), offending_line(proof)
    rule = lemma2_proof.statement
    line_number = first_use_of_rule(proof, rule)
    if debug:
        print('Testing inline_proof_once (test 2). In main proof:\n',
              proof, "Replacing line", line_number,
              'with the proof of following lemma proof:\n',
              str(lemma2_proof))
    inlined_proof = inline_proof_once(proof, line_number, lemma2_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == proof.rules.union(lemma2_proof.rules)
    newuse = uses_of_rule(inlined_proof, rule)
    olduse = uses_of_rule(proof, rule)
    assert newuse == olduse - 1, \
        "Uses of rule went from " + str(olduse) + " to " + str(newuse)
    assert inlined_proof.is_valid(), offending_line(inlined_proof)

    for count in range(3):
        # Test inlining lemma1_proof into result of previous inlining
        proof = inlined_proof
        assert proof.is_valid(), offending_line(proof)
        rule = lemma1_proof.statement
        assert uses_of_rule(proof, rule) == 3 - count
        line_number = first_use_of_rule(proof, rule)
        if debug:
            print('Testing inline_proof_once (test ' + str(3 + count) +
                  '). In main proof:\n', proof, "Replacing line", line_number,
                  'with the proof of following lemma proof:\n',
                  str(lemma1_proof))
        inlined_proof = inline_proof_once(proof, line_number, lemma1_proof)
        if debug:
            print("\nGot:", inlined_proof)
        assert inlined_proof.statement == proof.statement
        assert inlined_proof.rules == proof.rules.union(lemma1_proof.rules)
        newuse = uses_of_rule(inlined_proof, rule)
        olduse = uses_of_rule(proof, rule)
        assert newuse == olduse - 1, \
            "Uses of rule went from " + str(olduse) + " to " + str(newuse)
        assert inlined_proof.is_valid(), offending_line(inlined_proof)

    statement = InferenceRule([Formula.parse('(x&y)'), Formula.parse('(w&z)')],
                              Formula.parse('((y&x)&(z&w))'))
    RA = InferenceRule([Formula.parse('p'), Formula.parse('q')],
                       Formula.parse('(p&q)'))
    RB = InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)'))
    lines = [Proof.Line(Formula.parse('(x&y)')),
             Proof.Line(Formula.parse('(y&x)'), RB, [0]),
             Proof.Line(Formula.parse('(w&z)')),
             Proof.Line(Formula.parse('(z&w)'), RB, [2]),
             Proof.Line(Formula.parse('((y&x)&(z&w))'), RA, [1, 3])]
    proof = Proof(statement, {RA, RB}, lines)
    lem_proof = prove_and_commutativity()
    assert proof.is_valid(), offending_line(proof)
    assert lem_proof.is_valid(), offending_line(lem_proof)
    line_number = first_use_of_rule(proof, RB)
    if debug:
        print('Testing inline_proof_once (final). In main proof:\n',
              proof, "Replacing line", line_number,
              'with the proof of following lemma proof:\n',
              str(lem_proof))
    inlined_proof = inline_proof_once(proof, line_number, lem_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == proof.rules.union(lem_proof.rules)
    newuse = uses_of_rule(inlined_proof, RB)
    olduse = uses_of_rule(proof, RB)
    assert newuse == olduse - 1, \
        "Uses of rule went from " + str(olduse) + " to " + str(newuse)
    assert inlined_proof.is_valid(), offending_line(inlined_proof)
    #print(proof)
    #print("__________________________")
    #print(lem_proof)
    #print("__________________________")
    #print(inlined_proof)
    #print("__________________________")
    #print(inlined_proof.statement)
    #print(proof.statement)
    #print("__________________________")
    #print(inlined_proof.rules)
    #print(proof.rules.union(lem_proof.rules))



def uses_of_rule(proof, rule):
    """Returns the number of lines in which the given proof uses the given rule.
    """
    i=0
    for line in proof.lines:
        if (not line.is_assumption()) and line.rule == rule:
            i = i+1
    return i

def first_use_of_rule(proof, rule):
    """Returns the number of the first line in which the given proof uses the
    given rule."""
    i=0
    for i in range(len(proof.lines)):
        if (not proof.lines[i].is_assumption()) and proof.lines[i].rule == rule:
            return i
    assert False

def test_inline_proof(debug=False):
    lemma1_proof = DISJUNCTION_COMMUTATIVITY_PROOF
    lemma2_proof = DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF
    assert lemma1_proof.is_valid(), offending_line(lemma1_proof)
    assert lemma2_proof.is_valid(), offending_line(lemma2_proof)
    
    rule0 = InferenceRule([Formula.parse('((x|y)|z)')],
                          Formula.parse('(x|(y|z))'))
    rule1 = InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)'))
    rule2 = InferenceRule([], Formula.parse('(~p|p)'))

    # A proof that uses both disjunction commutativity (lemma 1) and
    # disjunction right associativity (lemma2), whose proof in turn also uses
    # disjunction commutativity (lemma 1).
    proof = Proof(
        InferenceRule([Formula.parse('((p|q)|r)')],
                      Formula.parse('((r|p)|q)')),
        {rule0, rule1, rule2},
        [Proof.Line(Formula.parse('((p|q)|r)')),
         Proof.Line(Formula.parse('(p|(q|r))'), rule0, [0]),
         Proof.Line(Formula.parse('((q|r)|p)'), rule1, [1]),
         Proof.Line(Formula.parse('(q|(r|p))'), rule0, [2]),
         Proof.Line(Formula.parse('((r|p)|q)'), rule1, [3])])

    # Test inlining lemma1_proof into (lemma2_proof into proof)

    if debug:
        print('Testing inline_proof (#1) for the following main proof:\n' +
              str(proof) + '\nand the following lemma proof:\n' +
              str(lemma2_proof))
    inlined_proof = inline_proof(proof, lemma2_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == \
           proof.rules.union(lemma2_proof.rules).difference(
               {lemma2_proof.statement}), \
            "Rule are: " + str(inlined_proof.rules)
    assert inlined_proof.is_valid(), offending_line(inlined_proof)

    if debug:
        print('Testing inline_proof (#2) for the following main proof:\n' +
              str(inlined_proof) + '\nand the following lemma proof:\n' +
              str(lemma1_proof))
    inlined_proof = inline_proof(inlined_proof, lemma1_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == proof.rules.\
                                  union(lemma2_proof.rules).\
                                  difference({lemma2_proof.statement}).\
                                  union(lemma1_proof.rules).\
                                  difference({lemma1_proof.statement})
    assert inlined_proof.is_valid(), offending_line(inlined_proof)


    # Test inlining lemma2_proof into (lemma1_proof into proof)

    if debug:
        print('Testing inline_proof (#3) for the following main proof:\n' +
              str(proof) + '\nand the following lemma proof:\n' +
              str(lemma1_proof))
    inlined_proof = inline_proof(proof, lemma1_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == \
           proof.rules.union(lemma1_proof.rules).difference(
               {lemma1_proof.statement})
    assert inlined_proof.is_valid(), offending_line(inlined_proof)

    if debug:
        print('Testing inline_proof (#4) for the following main proof:\n' +
              str(inlined_proof) + '\nand the following lemma proof:\n' +
              str(lemma2_proof))
    inlined_proof = inline_proof(inlined_proof, lemma2_proof)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == proof.rules.\
                                  union(lemma1_proof.rules).\
                                  difference({lemma1_proof.statement}).\
                                  union(lemma2_proof.rules).\
                                  difference({lemma2_proof.statement})
    assert inlined_proof.is_valid(), offending_line(inlined_proof)


    # Test inlining (lemma1_proof into lemma2_proof) into
    # (lemma1_proof into proof)

    inlined_proof = inline_proof(proof, lemma1_proof) # Already tested above

    if debug:
        print('Testing inline_proof (#5) for the following main proof:\n' +
              str(lemma2_proof) + '\nand the following lemma proof:\n',
              str(lemma1_proof))
    inlined_lemma = inline_proof(lemma2_proof, lemma1_proof)
    if debug:
        print("\nGot:", inlined_lemma)
    assert inlined_lemma.statement == lemma2_proof.statement
    assert inlined_lemma.rules == \
           lemma1_proof.rules.union(lemma2_proof.rules).difference(
               {lemma1_proof.statement})
    assert inlined_lemma.is_valid(), offending_line(inlined_lemma)

    if debug:
        print('Testing inline_proof (#6) for the following main proof:\n' +
              str(inlined_proof) + '\nand the following lemma proof:\n' +
              str(inlined_lemma))
    inlined_proof = inline_proof(inlined_proof, inlined_lemma)
    if debug:
        print("\nGot:", inlined_proof)
    assert inlined_proof.statement == proof.statement
    assert inlined_proof.rules == \
           inlined_lemma.rules.union(inlined_proof.rules).difference(
               {lemma2_proof.statement})
    assert inlined_proof.is_valid(), offending_line(inlined_proof)


def test_ex4(debug=False):
    test_variables(debug)
    test_specialize(debug)
    test_merge_specialization_maps(debug)
    test_formula_specialization_map(debug)
    test_specialization_map(debug)
    test_rule_for_line(debug)
    test_is_line_valid(debug)
    test_is_valid(debug)

def test_ex5(debug=False):
    test_prove_specialization(debug)
    test_inline_proof_once(debug)
    test_inline_proof(debug)

def test_all(debug=False):
    test_ex4(debug)
    test_ex5(debug)
