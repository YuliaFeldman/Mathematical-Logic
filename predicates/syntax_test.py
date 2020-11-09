# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax_test.py

"""Tests for the predicates.syntax module."""

from predicates.syntax import *

def test_term_repr(debug=False):
    s = 'f(s(0),x)'
    if debug:
        print('Testing representation of the term', s)
    term = Term('f', [Term('s', [Term('0')]), Term('x')])
    assert str(term) == s
    #print(term)

def test_term_parse_prefix(debug=False):
    for s in ['a', 'a,g(x))', 'g(x))', 'f(a,g(x))', 's(0)))', 's(s(0)))',
              's(s(s(_)))', '_,s(y))', 's(y))', 'plus(x,s(y))',
              'plus(x,plus(y,z)),a']:
        if debug:
            print('Parsing a prefix of', s, 'as a Term...')
        term, remainder = Term.parse_prefix(s)
        if debug:
            print('... and got', term, 'with unparsed remainder', remainder)
        assert str(term)+remainder == s 

    s = 'x12'
    if debug:
        print('Parsing a prefix of', s, 'as a Term...')
    term, remainder = Term.parse_prefix(s)
    if debug:
        print('... and got', term, 'with unparsed remainder', remainder)
    assert str(term) == 'x12' and remainder == ''

    s = 'c12'
    if debug:
        print('Parsing a prefix of', s, 'as a Term...')
    term, remainder = Term.parse_prefix(s)
    if debug:
        print('... and got', term, 'with unparsed remainder', remainder)
    assert str(term) == 'c12' and remainder == ''

    s = '_12'
    if debug:
        print('Parsing a prefix of', s, 'as a Term...')
    term, remainder = Term.parse_prefix(s)
    if debug:
        print('... and got', term, 'with unparsed remainder', remainder)
    assert str(term) == '_' and remainder == '12'

def test_term_parse(debug=False):
    for s in ['a12', 'f(a,g(x))', 's(s(s(0)))', 'plus(x,s(_))',
              'plus(plus(x,plus(y,z)),w)']:
        if debug:
            print('Parsing', s, 'as a Term...')
        term = Term.parse(s)
        if debug:
            print('... and got', term)
        assert str(term) == s 

def test_term_constants(debug=False):
    for s,expected_constants in [
            ['x', set()], ['0', {'0'}], ['s(s(c))', {'c'}],
            ['s(c,_)', {'c', '_'}], ['f(x,g(y,1,0),1)', {'0', '1'}],
            ['s(plus(times(d,c),times(d,s(s(x)))))', {'c', 'd'}]]:
        constants = Term.parse(s).constants()
        if debug:
            print('The constants in', s, 'are', constants)
        assert constants == expected_constants

def test_term_variables(debug=False):
    for s,expected_variables in [
            ['0', set()], ['x', {'x'}], ['s(s(x))', {'x'}],
            ['f(x,g(y,x,0),1)', {'x', 'y'}],
            ['s(plus(times(zz,x),times(x,s(s(0)))))', {'x', 'zz'}]]:
        variables = Term.parse(s).variables()
        if debug:
            print('The variables in', s, 'are', variables)
        assert variables == expected_variables

def test_term_functions(debug=False):
    for s,expected in [['3', set()], ['c17', set()], ['y25', set()],
                       ['plus(4,6)', {('plus', 2)}],
                       ['plus(times(plus(2,4),c8,d7),plus(minus(x),5))',
                        {('plus', 2), ('minus', 1), ('times', 3)}]]:
        functions = Term.parse(s).functions()
        if debug:
            print('The functions in', s, 'are', functions)
        assert functions == expected

def test_term_substitute(debug=False):
    # Test substitution of a single variable
    substitution_map = {'x': Term.parse('g(1)')}
    for s,expected in [['0', '0'], ['x', 'g(1)'], ['f(x)', 'f(g(1))'],
                       ['s(s(x))', 's(s(g(1)))'],
                       ['f(x,g(y,x,0),1)', 'f(g(1),g(y,g(1),0),1)'],
                       ['f(x,0,g(x))', 'f(g(1),0,g(g(1)))']]:
        result = Term.parse(s).substitute(substitution_map)
        if debug:
            print("Substituting 'g(1)' for 'x' in", s, 'gives', result)
        assert str(result) == expected

    # Test substitution of a single constant
    substitution_map = {'c': Term.parse('g(1)')}
    for s,expected in [['0', '0'], ['c', 'g(1)'], ['f(c)', 'f(g(1))'],
                       ['s(s(c))', 's(s(g(1)))'],
                       ['f(c,g(y,c,0),1)', 'f(g(1),g(y,g(1),0),1)'],
                       ['f(c,0,g(c))', 'f(g(1),0,g(g(1)))']]:
        result = Term.parse(s).substitute(substitution_map)
        if debug:
            print("Substituting 'g(1)' for 'c' in", s, 'gives', result)
        assert str(result) == expected

    # Test a more complex substitution
    substitution_map = {'c':Term.parse('g(f(x))'), 'x':Term.parse('f(c,x)'),
                        '_':Term.parse('d')}
    result = Term.parse('h(c,f(x,_))').substitute(substitution_map, {'y'})
    if debug:
        print('Substituting', substitution_map, " in 'h(c,f(x, _))' gives",
              result)
    assert str(result) == 'h(g(f(x)),f(f(c,x),d))'

    # Test illegal substitutions
    term = Term.parse('h(c,f(x))')
    for substitution_map,forbidden_variables,variable_name in [
        ({'c': Term.parse('g(f(x))'), 'x': Term.parse('f(c,y)')}, {'z','y'},
         'y'),
        ({'c': Term.parse('g(f(y))'), 'x': Term.parse('f(c,x)')}, {'y','z'},
         'y')]:
        if debug:
            print('Substituting', substitution_map, "in", term,
                  'with forbidden variables', forbidden_variables)
        try:
            result = term.substitute(substitution_map, forbidden_variables)
            assert False, 'Expected exception'
        except ForbiddenVariableError as e:
            if debug:
                print('Threw a ForbiddenVariableError as expected')
            assert e.variable_name == variable_name

def test_formula_repr(debug=False):
    s = '(Ax[plus(x,y)=0]->~R(v,c7))'
    if debug:
        print('Testing representation of the formula', s)
    formula = Formula('->',
                      Formula('A', 'x',
                              Formula('=',
                                      [Term('plus', [Term('x'), Term('y')]),
                                       Term('0')])),
                      Formula('~', Formula('R', [Term('v'), Term('c7')])))
    assert str(formula) == s

def test_formula_parse_prefix(debug=False):
    for s in ['0=_', 'R(x)|Q(y))', 'Q(y))', '(R(x)|Q(y))', '0=0&1=1)', '1=1)',
              '(0=0&1=1)', 'R(0)&0=0)|Ex[Q(x)])', '0=0)|Ex[Q(x)])',
              '(R(0)&0=0)|Ex[Q(x)])', 'Q(x)])', 'Ex[Q(x)])',
              '((R(0)&0=0)|Ex[Q(x)])', 'R(x,y)', 'PLUS(s(x),y,s(plus(x,y)))',
              'R(x8,x7,c)]', 'Ax8[R(x8,x7,c)]', 'R(x,y)]]', 'Ay[R(x,y)]]]',
              'Ex[Ay[R(x,y)]]', 'R(x)', '~R(x)', 'Q(x)]', '~Q(x)]', 'Ax[~Q(x)]',
              '~Ax[~Q(x)]', '~~Ax[~Q(x)]', 'plus(_,y)=plus(y,x)]]',
              'Ay[plus(x,y)=plus(y,x)]]', 'Ax[Ay[plus(x,y)=plus(y,x)]]',
              '~x=f(y)', 'Q()&R(x))', 'R(x))', '(Q()&R(x))']:
        if debug:
            print('Parsing a prefix of', s, 'as a first-order formula...')
        formula, remainder = Formula.parse_prefix(s)
        if debug:
            print('.. and got', formula, 'with unparsed remainder', remainder)
        assert str(formula) + remainder == s

    s = '0=x12'
    if debug:
        print('Parsing a prefix of', s, 'as a first-order formula...')
    formula, remainder = Formula.parse_prefix(s)
    if debug:
        print('... and got', formula, 'with unparsed remainder', remainder)
    assert str(formula) == '0=x12' and remainder == ''

    s = '0=_12'
    if debug:
        print('Parsing a prefix of', s, 'as a first-order formula...')
    formula, remainder = Formula.parse_prefix(s)
    if debug:
        print('... and got', formula, 'with unparsed remainder', remainder)
    assert str(formula) == '0=_' and remainder == '12'

def test_formula_parse(debug=False):
    for s in ['_=0', '(R(x)|Q(y))', '(0=0&1=1)', '((R(0)&0=0)|Ex[Q(x)])',
              'R(x,y)', 'PLUS(s(x),y,s(plus(x,y)))', 'Ax8[R(x8,x7,c)]',
              'Ex[Ay[R(x,y)]]', '~R(x)', '~~Ax[~Q(x)]',
              'Ax[Ay[plus(x,y)=plus(y,_)]]', '~x=f(y)', '(Q()&R(x))']:
        if debug:
            print('Parsing', s, 'as a first-order formula...')
        formula = Formula.parse(s)
        if debug:
            print('.. and got', formula)
        assert str(formula) == s

def test_formula_constants(debug=False):
    for s,expected_constants in [
            ['x=x', set()], ['x=0', {'0'}], ['c=_', {'c', '_'}],
            ['R(s(s(c)))', {'c'}], ['Ax[~x=1]', {'1'}],
            ['Ax[(x=2|x=1)]', {'1', '2'}], ['Ey[R(s(s(d)))]', {'d'}],
            ['Ax[Ez[f(x,g(y,x,0),1)=d]]', {'0', '1', 'd'}]]:
        constants = Formula.parse(s).constants()
        if debug:
            print('The free constants in', s, 'are', constants)
        assert constants == expected_constants

def test_formula_variables(debug=False):
    for s,expected_variables in [
            ['0=0', set()], ['x=0', {'x'}], ['R(s(s(x)))', {'x'}],
            ['Ax[~x=1]', {'x'}], ['Ax[(x=2|x=1)]', {'x'}], 
            ['Ey[R(s(s(x)))]', {'x', 'y'}], ['Ex[R(s(s(x)))]', {'x'}],
            ['(Q(v)->Ax[Ez[f(x,g(y,x,0),1)=w]])', {'v', 'w', 'x', 'y', 'z'}],
            ['(R(s(plus(times(zz,x),times(x,s(s(0))))))|Ex[Q(x,w)])',
             {'x', 'zz', 'w'}]]:
        variables = Formula.parse(s).variables()
        if debug:
            print('The free variables in', s, 'are', variables)
        assert variables == expected_variables

def test_free_variables(debug=False):
    for s,expected_variables in [
            ['0=0', set()], ['x=0', {'x'}], ['R(s(s(x)))', {'x'}],
            ['Ax[~x=1]', set()], ['Ax[(x=2|x=1)]', set()], 
            ['Ey[R(s(s(x)))]', {'x'}], ['Ex[R(s(s(x)))]', set()],
            ['(Q(v)->Ax[Ez[f(x,g(y,x,0),1)=w]])', {'v', 'w', 'y'}],
            ['(R(s(plus(times(zz,x),times(x,s(s(0))))))|Ex[Q(x,w)])',
             {'x', 'zz', 'w'}]]:
        variables = Formula.parse(s).free_variables()
        if debug:
            print('The free variables in', s, 'are', variables)
        assert variables == expected_variables

def test_formula_functions(debug=False):
    for s,expected in [
            ['c17=3', set()],
            ['minus(times(2,5))=s(3)', {('minus', 1), ('times', 2), ('s', 1)}],
            ['T(35,2,4)', set()],
            ['Q(25,x,minus(times(2,5)),s(3))',
             {('minus', 1), ('times', 2), ('s', 1)}],
            ['(R(23,minus(times(2,5)))|Q(c,s(3),d))',
             {('minus', 1), ('times', 2), ('s', 1)}],
            ['(R(23,minus(times(2,5)))&Q(c,s(3),d))',
             {('minus', 1), ('times', 2), ('s', 1)}],
            ['(R(23,minus(times(2,5)))->Q(c,s(3),d))',
             {('minus', 1), ('times', 2), ('s', 1)}],
            ['Ax[T(35,x,4)]', set()],
            ['Ex[Q(25,x,minus(times(2,5)),s(3))]',
             {('minus', 1), ('times', 2), ('s', 1)}],
            ['((P(c,f(2,3,5))&~Ax[Q(g(1))])|(S()|(G(1,x,h(1,2,3,4,6))->a=i(33))))',
             {('f', 3), ('g', 1), ('h', 5), ('i', 1)}]]:
        functions = Formula.parse(s).functions()
        if debug:
            print('The functions in', s, 'are', functions)
        assert functions == expected

def test_relations(debug=False):
    for s,expected in [
            ['c17=3', set()],
            ['minus(times(2,5))=s(3)', set()],
            ['T(35,2,4)', {('T', 3)}],
            ['Q(25,x,minus(times(2,5)),s(3))', {('Q', 4)}],
            ['(R(23,minus(times(2,5)))|Q(c,s(3),d))', {('R', 2), ('Q', 3)}],
            ['(R(23,minus(times(2,5)))&Q(c,s(3),d))', {('R', 2), ('Q', 3)}],
            ['(R(23,minus(times(2,5)))->Q(c,s(3),d))', {('R', 2), ('Q', 3)}],
            ['Ax[T(35,x,4)]', {('T', 3)}],
            ['Ex[Q(25,x,minus(times(2,5)),s(3))]', {('Q', 4)}],
            ['((P(c,f(2,3,5))&~Ax[Q(g(1))])|(S()|(G(1,x,h(1,2,3,4,6))->a=i(33))))',
             {('P', 2), ('Q', 1), ('S', 0), ('G', 3)}]]:
        relations = Formula.parse(s).relations()
        if debug:
            print('The relations in', s, 'are', relations)
        assert relations == expected

def test_formula_substitute(debug=False):
    for s,substitution,expected in [
            ('R(x,y)', {'x':'f(0)'}, 'R(f(0),y)'),
            ('c=_', {'_': 'g(f(d))'}, 'c=g(f(d))'),
            ('(x=x|y=y)', {'y':'0'}, '(x=x|0=0)'),
            ('Ax[R(x,y)]', {'y':'z'}, 'Ax[R(x,z)]'),
            ('Ax[R(x,y)]', {'x':'z'}, 'Ax[R(x,y)]'),
            ('Ax[R(x,y)]', {'x':'z', 'y': 'w'}, 'Ax[R(x,w)]'),
            ('(x=x|Ex[R(x,y)])', {'x':'z'}, '(z=z|Ex[R(x,y)])'),
            ('R(c,y)', {'c':'f(0)'}, 'R(f(0),y)'),
            ('(x=x|c=c)', {'c':'0'}, '(x=x|0=0)'),
            ('Ax[R(x,c)]', {'c':'z'}, 'Ax[R(x,z)]'),
            ('(c=c|Ex[R(c,y)])', {'c':'z'}, '(z=z|Ex[R(z,y)])'),
            ('R(c,d)', {'c':'d','d':'c'}, 'R(d,c)'),
            ('Q(x,c)', {'x':'f(c,d)','c':'f(1,x)'}, 'Q(f(c,d),f(1,x))')]:
        formula = Formula.parse(s)
        substitution_map = {v: Term.parse(substitution[v])
                            for v in substitution.keys()}
        result = str(formula.substitute(substitution_map))
        if debug:
            print('Substituting', substitution_map, 'in', formula, 'yields',
                  result)
        assert result == expected

    for s,substitution,forbidden_variables,variable_name in [
            ('w=y', {'y':'x'}, {'x'}, 'x'),
            ('z=c', {'c':'f(x)'}, {'x'}, 'x'),
            ('Ex[x=y]', {'y':'x'}, set(), 'x'),
            ('Ex[c=y]', {'c':'g(x)'}, set(), 'x')]:
        formula = Formula.parse(s)
        substitution_map = {v: Term.parse(substitution[v])
                            for v in substitution.keys()}
        if debug:
            print('Substituting', substitution_map, 'in', formula)
        try:
            result = str(formula.substitute(substitution_map,
                                            forbidden_variables))
            assert False, 'Expected exception'
        except ForbiddenVariableError as e:
            if debug:
                print('Threw a ForbiddenVariableError as expected')
            assert e.variable_name == variable_name

def test_propositional_skeleton(debug=False):
    from logic_utils import fresh_variable_name_generator
    fresh_variable_name_generator._reset_for_test()

    for s,expected,expected_map in [
            ['x=y', 'z1', {'z1': Formula.parse('x=y')}],
            ['R(x,c)', 'z2', {'z2': Formula.parse('R(x,c)')}],
            ['Ax[(R(x)|R(y))]', 'z3', {'z3': Formula.parse('Ax[(R(x)|R(y))]')}],
            ['~1=1', '~z4', {'z4': Formula.parse('1=1')}],
            ['(Ax[P(x)]&Ax[P(x)])', '(z5&z5)',
             {'z5': Formula.parse('Ax[P(x)]')}],
            ['(0=0&1=1)', '(z6&z7)',
             {'z6': Formula.parse('0=0'), 'z7': Formula.parse('1=1')}],
            ['((R(0)|R(1))&~R(0))', '((z8|z9)&~z8)',
             {'z8': Formula.parse('R(0)'), 'z9': Formula.parse('R(1)')}]]:
        skeleton, substitution_map = \
            Formula.parse(s).propositional_skeleton()
        if debug:
            print('The skeleton of', s, 'is', skeleton,
                  'with map', substitution_map)
        assert (str(skeleton), substitution_map) == (expected, expected_map)

def test_from_propositional_skeleton(debug=False):
    for expected,skeleton,substitution_map in [
            ['x=y', 'z1', {'z1': Formula.parse('x=y')}],
            ['R(x,c)', 'z2', {'z2': Formula.parse('R(x,c)')}],
            ['Ax[(R(x)|R(y))]', 'z3', {'z3': Formula.parse('Ax[(R(x)|R(y))]')}],
            ['~1=1', '~z4', {'z4': Formula.parse('1=1')}],
            ['(Ax[P(x)]&Ax[P(x)])', '(z5&z5)',
             {'z5': Formula.parse('Ax[P(x)]')}],
            ['(0=0&1=1)', '(z6&z7)',
             {'z6': Formula.parse('0=0'), 'z7': Formula.parse('1=1')}],
            ['((R(0)|R(1))&~R(0))', '((z8|z9)&~z8)',
             {'z8': Formula.parse('R(0)'), 'z9': Formula.parse('R(1)')}]]:
        formula = Formula.from_propositional_skeleton(
            PropositionalFormula.parse(skeleton), substitution_map)
        if debug:
            print('Substituting', substitution_map, 'into', skeleton,
                  'returned', formula)
        assert str(formula) == expected

def test_ex7(debug=False):
    test_term_repr(debug) 
    test_formula_repr(debug)
    test_term_parse_prefix(debug)
    test_term_parse(debug)
    test_formula_parse_prefix(debug)
    test_formula_parse(debug)
    test_term_constants(debug)
    test_term_variables(debug)
    test_term_functions(debug)
    test_formula_constants(debug)
    test_formula_variables(debug)
    test_free_variables(debug)
    test_formula_functions(debug)
    test_relations(debug)

def test_ex9(debug=False):
    test_term_substitute(debug)
    test_formula_substitute(debug)
    test_propositional_skeleton(debug)
    test_from_propositional_skeleton(debug)

def test_all(debug=False):
    test_ex7(debug)
    test_ex9(debug)
