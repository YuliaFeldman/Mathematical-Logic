# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax_test.py

"""Tests for the propositions.syntax module."""

from logic_utils import frozendict

from propositions.syntax import *

# Testing for Chapter 1

def test_repr(debug=False):
    if debug:
        print("Testing representation of formula 'x12'")
    assert str(Formula('x12')) == 'x12'
    if debug:
        print("Testing representation of formula 'T'")
    assert str(Formula('T')) == 'T'
    if debug:
        print("Testing representation of formula '~~F'")
    assert str(Formula('~', Formula('~', Formula('F')))) == '~~F'
    if debug:
        print("Testing representation of formula '(p|p)'")
    assert str(Formula('|',Formula('p'),Formula('p'))) == '(p|p)'
    if debug:
        print("Testing representation of formula '~(p&q7)'")
    assert str(Formula('~', Formula('&', Formula('p'), Formula('q7')))) == '~(p&q7)'
    if debug:
        print("Testing representation of formula '((p->q)->(~q->~p))'")
    assert str(Formula("->", Formula("->", Formula("p"), Formula("q")), \
                             Formula("->", Formula("~", Formula("q")), Formula("~", Formula("p"))))) == \
           '((p->q)->(~q->~p))'

def test_variables(debug=False):
    for f, vs in [(Formula('T'), set()),
                  (Formula('x1234'), {'x1234'}),
                  (Formula('~',Formula('r')), {'r'}),
                  (Formula('->',Formula('x'), Formula('y')), {'x','y'}),
                  (Formula('&', Formula('F'), Formula('~', Formula('T'))), set()),
                  (Formula('|', Formula('~', Formula('->', Formula('p1'), Formula('p2'))), Formula('F')), {'p1','p2'}),
                  (Formula('~', Formula('~', Formula('|', Formula('x'), Formula('~',Formula('x'))))), {'x'})]:
        if debug:
            print("Testing variables of", f)
        assert f.variables() == vs

def test_operators(debug=False):
    for f, ops in [(Formula('T'), {'T'}),
                   (Formula('x1234'), set()),
                   (Formula('~',Formula('r')), {'~'}),
                   (Formula('->',Formula('x'), Formula('y')), {'->'}),
                   (Formula('&', Formula('F'), Formula('~', Formula('T'))), {'F', 'T', '&', '~'}),
                   (Formula('|', Formula('~', Formula('->', Formula('p1'), Formula('p2'))), Formula('F')), {'|', '~', '->', 'F'}),
                   (Formula('~', Formula('~', Formula('|', Formula('x'), Formula('~',Formula('x'))))),{'|', '~'})]:
        if debug:
            print ("Testing operators of", f)
        assert f.operators() == ops

parsing_tests = [('', None, ''),
                 ('x', 'x', ''),
                 ('T', 'T', ''),
                 ('a', None, ''),
                 (')', None, ''),
                 ('x&', 'x', '&'),
                 ('p3&y', 'p3', '&y'),
                 ('F)', 'F', ')'),
                 ('~x', '~x', ''),
                 ('~', None, ''),
                 ('x2', 'x2', ''),
                 ('x|y', 'x', '|y'),
                 ('(p|x13)', '(p|x13)', ''),
                 ('((p|x13))', None, ''),
                 ('x13->x14', 'x13', '->x14'),
                 ('(x13->x14)', '(x13->x14)', ''),
                 ('(x&y',None,''),
                 ('(T)',None,''),
                 ('(x&&y)', None, ''),
                 ('-|x',None,''),
                 ('-->',None,''),
                 ('(q~p)',None,''),
                 ('(~F)', None, ''),
                 ('(r&(y|(z->w)))','(r&(y|(z->w)))',''),
                 ('~~~x~~','~~~x','~~'),
                 ('(((~T->s45)&s45)|~y)', '(((~T->s45)&s45)|~y)' ,''),
                 ('((p->q)->(~q->~p))->T)','((p->q)->(~q->~p))','->T)'),
                 ('((p->q)->(~q->~p)->T)',None,''),
                 ('(x|y|z)', None, ''),
                 ('~((~x17->p)&~~(~F|~p))', '~((~x17->p)&~~(~F|~p))', '')]

def test_parse_prefix(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests:
        if debug:
            print("Testing parsing prefix of", s)
        ff, rr = Formula.parse_prefix(s)
        if ff is None:
            assert f is None, "parse_prefix returned error: " + rr
            if debug:
                print("... parse_prefix correctly returned error message:", rr)
            continue
        assert type(ff) is Formula
        assert type(rr) is str
        ff = str(ff)
        assert ff == f, "parse_prefix parsed " + str(ff)
        assert rr == r, "parse-Prefix did not parse " + rr
                     
def test_is_formula(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests:
        if debug:
            print("Testing is formula on", s)
        if f != None and r == '':
            assert Formula.is_formula(s)
        else:
            assert not Formula.is_formula(s)
                     
def test_parse(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests:
        if f is None or r != '':
            continue
        if debug:
            print("Testing parsing ", s)
        ff = Formula.parse(s)
        assert type(ff) is Formula
        assert str(ff) == f

# Tests for optional tasks in Chapter 1

def test_polish(debug=False):
    if debug:
        print("Testing polish of formula 'x12'")
    assert Formula('x12').polish() == 'x12'
    if debug:
        print("Testing polish of formula '|pp' (in infix: '(p|p)')")
    assert Formula('|', Formula('p'), Formula('p')).polish() == '|pp'
    if debug:
        print("Testing polish of formula '~&pq7' (in infix: '~(p&q7)')")
    assert Formula('~', Formula('&', Formula('p'), Formula('q7'))).polish() == '~&pq7'

def test_parse_polish(debug=False):
    for polish in ['p', '~x12', '&xy', '~~|x~T', '|&x1~x2F']:
        if debug:
            print("Testing polish parsing of formula", polish)
        assert Formula.parse_polish(polish).polish() == polish

# Tests for Chapter 3

def test_repr_all_operators(debug=False):
    if debug:
        print("Testing representation of formula '(x12+x12)'")
    assert str(Formula('+',Formula('x12'),Formula('x12'))) == '(x12+x12)'
    if debug:
        print("Testing representation of formula '(T-|F)'")
    assert str(Formula('-|',Formula('T'),Formula('F'))) == '(T-|F)'
    if debug:
        print("Testing representation of formula '(p-&p)'")
    assert str(Formula('-&',Formula('p'),Formula('p'))) == '(p-&p)'
    if debug:
        print("Testing representation of formula '(p<->p)'")
    assert str(Formula('<->',Formula('p'),Formula('p'))) == '(p<->p)'
    if debug:
        print("Testing representation of formula '(p<->~p)'")
    assert str(Formula('<->',Formula('p'),Formula('~',Formula('p')))) == '(p<->~p)'
    if debug:
        print("Testing representation of formula '~(p~&q7)'")
    assert str(Formula('~', Formula('-&', Formula('p'), Formula('q7')))) == '~(p-&q7)'
    if debug:
        print("Testing representation of formula '(~(p+q)<->(~q<->~p))'")
    assert str(Formula("<->", Formula('~', Formula("+", Formula("p"), Formula("q"))), \
                              Formula("<->", Formula("~", Formula("q")), Formula("~", Formula("p"))))) == \
           '(~(p+q)<->(~q<->~p))'
    if debug:
        print("Testing representation of formula '(~(p1+q)|(~q-&~p))'")
    assert str(Formula("|", Formula('~', Formula("+", Formula("p1"), Formula("q"))), \
                              Formula("-&", Formula("~", Formula("q")), Formula("~", Formula("p"))))) == \
           '(~(p1+q)|(~q-&~p))'

def test_variables_all_operators(debug=False):
    for f, vs in [ (Formula('T'), set()),
                   (Formula('x1234'), {'x1234'}),
                   (Formula('~',Formula('r')), {'r'}),
                   (Formula('<->',Formula('x'), Formula('y')), {'x','y'}),
                   (Formula('-&', Formula('F'), Formula('~', Formula('T'))), set()),
                   (Formula('-|', Formula('~', Formula('+', Formula('p1'), Formula('p2'))), Formula('F')), {'p1','p2'}),
                   (Formula('~', Formula('~', Formula('<->', Formula('x'), Formula('~',Formula('x'))))),{'x'}) ]:
        if debug:
            print ("Testing variables of", f)
        assert f.variables() == vs

def test_operators_all_operators(debug=False):
    for f, ops in [ (Formula('T'), {'T'}),
                   (Formula('x1234'), set()),
                   (Formula('~',Formula('r')), {'~'}),
                   (Formula('<->',Formula('x'), Formula('y')), {'<->'}),
                   (Formula('-&', Formula('F'), Formula('~', Formula('T'))), {'F', 'T', '-&', '~'}),
                   (Formula('-|', Formula('~', Formula('+', Formula('p1'), Formula('p2'))), Formula('F')), {'-|', '~', '+', 'F'}),
                   (Formula('->', Formula('~', Formula('+', Formula('p1'), Formula('p2'))), Formula('F')), {'->', '~', '+', 'F'}),
                   (Formula('~', Formula('~', Formula('+', Formula('x'), Formula('~',Formula('x'))))),{'+', '~'}) ]:
        if debug:
            print ("Testing operators of", f)
        assert f.operators() == ops

parsing_tests_all_operators = [
                ('x+', 'x', '+'),
                ('~x', '~x', ''),
                ('x+y', 'x', '+y'),
                ('(p+x13)', '(p+x13)', ''),
                ('x13-|x14', 'x13', '-|x14'),
                ('(x13-&x14)', '(x13-&x14)', ''),
                ('(x+y',None,''),
                ('(x++y)', None, ''),
                ('-&x',None,''),
                ('<->',None,''),
                ('(r-&(y-|(z<->w)))','(r-&(y-|(z<->w)))',''),
                ('(((~T<->s45)&s45)+~y)', '(((~T<->s45)&s45)+~y)' ,''),
                ('((p->q)<->(~q->~p))->T)','((p->q)<->(~q->~p))','->T)'),
                ('((p<->q)->(~q<->~p)->T)',None,''),
                ('(x|y+z)', None, ''),
                ('(x--y)', None, ''),
                ('(x&-y)', None, ''),
                ('(x<>y)', None, ''),
                ('x<--y', 'x', '<--y'),
                ('~((~x17->p)-&~~(~F<->~p))', '~((~x17->p)-&~~(~F<->~p))', '')]

def test_parse_prefix_all_operators(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests_all_operators:
        if debug:
            print("Testing parsing prefix of", s)
        ff, rr = Formula.parse_prefix(s)
        if ff is None:
            assert f is None, "parse_prefix returned error: " + rr
            if debug:
                print("... parse_prefix correctly returned error message:", rr)
            continue
        assert type(ff) is Formula
        assert type(rr) is str
        ff = str(ff)
        assert ff == f, "parse_prefix parsed " + str(ff)
        assert rr == r, "parse-Prefix did not parse " + rr
                     
def test_is_formula_all_operators(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests_all_operators:
        if debug:
            print("Testing is formula on", s)
        if f != None and r == '':
            assert Formula.is_formula(s)
        else:
            assert not Formula.is_formula(s)
                     
def test_parse_all_operators(debug=False):
    if(debug):
        print()
    for s, f, r in parsing_tests_all_operators:
        if f is None or r != '':
            continue
        if debug:
            print("Testing parsing ", s)
        ff = Formula.parse(s)
        assert type(ff) is Formula
        assert str(ff) == f

def test_substitute_variables(debug=False):
    #           f         d              result
    tests = [ ('v',       {},             'v'),
              ('v',      {'v':'p'},       'p'),
              ('(F->v12)', {'v12':'v11'}, '(F->v11)'),
              ('v',      {'q':'r', 'z':'w'}, 'v'),
              ('p',      {'p':'(q|q)'},   '(q|q)'),
              ('~v',     {'v':'(q|q)'},   '~(q|q)'),
              ('(~v|v)', {'v':'(q|q)'},   '(~(q|q)|(q|q))'),
              ('(q12->w)', {'q12':'T', 'w':'x'}, '(T->x)'),
              ('(v->w)', {'v':'T', 'w':'v'}, '(T->v)'),
              ('((~v&w)|(v->u))', {'v':'(~p->q)', 'u':'~~F'}, '((~(~p->q)&w)|((~p->q)->~~F))'),
              ('v2',     {'v': 'p'},      'v2')]
    for f, d, r in tests:
        if debug:
            print("Testing substituting variables according to", d, "in formula", f)
        f = Formula.parse(f)
        d = {k:Formula.parse(d[k]) for k in d}
        a = str(f.substitute_variables(frozendict(d)))
        assert a == r, "Incorrect answer:"+a
        
def test_substitute_operators(debug=False):
    #         f              d                   result
    tests = [ ("v",          {},                 "v"),
              ("(v|w)",      {"|":"(~p->q)"},    "(~v->w)"),
              ("(T|~F)",     {"|":"(~p->q)"},    "(~T->~F)"),
              ("(x|(y|z))",  {"|":"(~p->q)"},    "(~x->(~y->z))"),
              ("(x->y)",     {"->":"(p&(q|p))"}, "(x&(y|x))"),
              ("(q->r)",     {"->":"(p&(q|p))"}, "(q&(r|q))"),
              ("((p1|~p2)&(p3|T))", {"|":"(q&p)", "&":"~(p->q)"}, "~((~p2&p1)->(T&p3))"),
              ("(x&(y|z))",  {"&":"(q|p)"},      "((y|z)|x)"),
              ("~x", {"~":"(p->F)"}, "(x->F)"),
              ("~(x->~x)", {"~":"(p-|p)", "->":"(~p|q)"}, "((~x|(x-|x))-|(~x|(x-|x)))"),
              ("((x&y)&~z)", {"&":"~(~p|~q)"},  "~(~~(~x|~y)|~~z)"),
              ("T", {"T":"(p|~p)"}, "(p|~p)"),
              ("(x-|~F)", {"F":"(p&~p)", "-|":"~(p|q)"}, "~(x|~(p&~p))")]
    for f, d, r in tests:
        if debug:
            print("Testing substituting operators according to", d, "in formula", f)
        f = Formula.parse(f)
        d = {k:Formula.parse(d[k]) for k in d}
        a = str(f.substitute_operators(frozendict(d)))
        assert a == r, "Incorrect answer:"+a
               
def test_ex1(debug=False):
    test_repr(debug)
    test_variables(debug)
    test_operators(debug)
    test_parse_prefix(debug)
    test_is_formula(debug)
    test_parse(debug)
    
def test_ex1_opt(debug=False):
    test_polish(debug)
    test_parse_polish(debug)

def test_ex3(debug=False):
    assert is_binary('+'), "Change is_binary() before testing Chapter 3 tasks."
    test_repr_all_operators(debug)
    test_variables_all_operators(debug)
    test_operators_all_operators(debug)
    test_parse_prefix_all_operators(debug)
    test_is_formula_all_operators(debug)
    test_parse_all_operators(debug)    
    test_substitute_variables(debug)
    test_substitute_operators(debug)

def test_all(debug=False):
    test_ex1(debug)
    test_ex1_opt(debug)
    test_ex3(debug) 
