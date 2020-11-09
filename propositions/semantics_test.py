# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics_test.py

"""Tests for the propositions.semantics module."""

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.axiomatic_systems import *

def test_evaluate(debug=False):
    infix1 = '~(p&q7)'
    models_values1 = [
        ({'p': True,  'q7': False}, True),
        ({'p': False, 'q7': False}, True),
        ({'p': True,  'q7': True},  False)
    ]
    infix2 = '~~~x'
    models_values2 = [
        ({'x': True}, False),
        ({'x': False}, True)
    ]
    infix3 = '((x->y)&(~x->z))'
    models_values3 = [
        ({'x': True,  'y': False, 'z':True},  False),
        ({'x': False, 'y': False, 'z':True},  True),
        ({'x': True,  'y': True,  'z':False}, True)
    ]
    infix4 = '(T&p)'
    models_values4 = [
        ({'p': True},  True),
        ({'p': False}, False)
    ]
    infix5 = '(F|p)'
    models_values5 = [
        ({'p': True},  True),
        ({'p': False}, False)
    ]
    for infix,models_values in [[infix1, models_values1],
                                [infix2, models_values2],
                                [infix3, models_values3],
                                [infix4, models_values4],
                                [infix5, models_values5]]:
        formula = Formula.parse(infix)
        for model,value in models_values:
            if debug:
                print('Testing evaluation of formula', formula, 'in model',
                      model)
            assert evaluate(formula, frozendict(model)) == value

def test_all_models(debug=False):
    variables1 = ('p', 'q')
    models1 = [{'p': False, 'q': False}, \
               {'p': False, 'q': True},  \
               {'p': True,  'q': False}, \
               {'p': True,  'q': True} ]
    variables2  = ['x']
    models2 = [{'x': False}, {'x': True}]
    for variables,models in [[variables1, models1], [variables2, models2]]:
        if debug:
            print('Testing all models over', variables)
        assert list(all_models(variables)) == models

def test_truth_values(debug=False):
    for infix,variables,values in [
            ['~(p&q7)', ('p', 'q7'), [True, True, True, False]],
            ['(y|~x)',  ('y', 'x'),  [True, False, True, True]],
            ['~~~p',    ('p'),       [True, False]]]:
        formula = Formula.parse(infix)
        if debug:
            print('Testing the evaluation of', formula,
                  'on all models over its variables')
        tvals = list(truth_values(formula, tuple(all_models(variables))))
        assert tvals == values, \
               'Expected ' + str(values) + '; got ' + str(tvals)

def test_print_truth_table(debug=False):
    infix1 = '~r'
    table1 = '| r | ~r |\n' \
             '|---|----|\n' \
             '| F | T  |\n' \
             '| T | F  |\n'
    
    infix2 = '~(p&q7)'
    table2 = '| p | q7 | ~(p&q7) |\n' \
             '|---|----|---------|\n' \
             '| F | F  | T       |\n' \
             '| F | T  | T       |\n' \
             '| T | F  | T       |\n' \
             '| T | T  | F       |\n'

    infix3 = '~(q7&p)'
    table3 = '| p | q7 | ~(q7&p) |\n' \
             '|---|----|---------|\n' \
             '| F | F  | T       |\n' \
             '| F | T  | T       |\n' \
             '| T | F  | T       |\n' \
             '| T | T  | F       |\n'

    infix4 = '(x&(~z|y))'
    table4 = '| x | y | z | (x&(~z|y)) |\n' \
             '|---|---|---|------------|\n' \
             '| F | F | F | F          |\n' \
             '| F | F | T | F          |\n' \
             '| F | T | F | F          |\n' \
             '| F | T | T | F          |\n' \
             '| T | F | F | T          |\n' \
             '| T | F | T | F          |\n' \
             '| T | T | F | T          |\n' \
             '| T | T | T | T          |\n'

    __test_print_truth_table([infix1, infix2, infix3, infix4],
                             [table1, table2, table3, table4], debug)

def __test_print_truth_table(infixes, tables, debug):

    from io import StringIO
    import sys

    class PrintCapturer:
        """A helper class for capturing text printed to the standard output."""
        def __enter__(self):
            """Saves the standard output and replace it with a mock."""
            self._stdout = sys.stdout
            sys.stdout = self._stringio = StringIO()
            return self

        def __exit__(self, *args):
            """Stores the captured text, and restore the original standard
            output."""
            self.captured = self._stringio.getvalue()
            sys.stdout = self._stdout

    capturer = PrintCapturer()
    for infix,table in zip(infixes, tables):
        formula = Formula.parse(infix)
        if debug:
            print('Testing truth table of', formula)
        with capturer as output:
            print_truth_table(formula)
        if debug:
            print ('Printed:\n' + capturer.captured)
            print ('Expected:\n' + table)
        import re
        assert re.sub('[ -]+', ' ', capturer.captured) == \
               re.sub('[ -]+', ' ', table)

def test_is_tautology(debug=False):
    for infix,answer in [['~(p&q7)',   False], ['(x|~x)',       True],
                            ['(p->q)', False], ['(p->p)', True],
                            ['(F|T)',     True],  ['((y1|~y1)&T)', True],
                            ['((T&T)|F)', True],  ['F',            False],
                            ['x',         False], ['~y',           False],
                            ['((x->y)&((y->z)&(x&~z)))', False],
                            ['~((x->y)&((y->z)&(x&~z)))', True]]:
        formula = Formula.parse(infix)
        if debug:
            print('Testing whether', formula, 'is a tautology')
        assert is_tautology(formula) == answer

def test_is_contradiction(debug=False):
    for infix,answer in [['~(p&q7)',   False], ['~(x|~x)',       True],
                            ['(T->F)',     True],  ['((y1|~y1)&T)', False],
                            ['((T&T)|F)', False],  ['F',            True],
                            ['x',         False], ['~y',           False],
                            ['((x->y)&((y->z)&(x&~z)))', True]]:
        formula = Formula.parse(infix)
        if debug:
            print('Testing whether', formula, 'is a contradiction')
        assert is_contradiction(formula) == answer

def test_is_satisfiable(debug=False):
    for infix,answer in [['~(p&q7)',   True], ['~(x|~x)',       False],
                            ['(T->F)',     False],  ['((y1|~y1)&T)', True],
                            ['((T&T)|F)', True],  ['F',            False],
                            ['x',         True], ['~y',           True],
                            ['((x->y)&((y->z)&(x&~z)))', False]]:
        formula = Formula.parse(infix)
        if debug:
            print('Testing whether', formula, 'is satisfiable')
        assert is_satisfiable(formula) == answer

def test_synthesize_for_model(debug=False):
    all_models1 = [{'x': False},
                   {'x': True}]
    all_models2 = [{'p': False, 'q': False},
                   {'p': False, 'q': True},
                   {'p': True,  'q': False},
                   {'p': True,  'q': True}]
    all_models3 = [{'r1': False, 'r12': False, 'p37': False},
                   {'r1': False, 'r12': False, 'p37': True},
                   {'r1': False, 'r12': True, 'p37': False},
                   {'r1': False, 'r12': True, 'p37': True},
                   {'r1': True, 'r12': False, 'p37': False},
                   {'r1': True, 'r12': False, 'p37': True},
                   {'r1': True, 'r12': True, 'p37': False},
                   {'r1': True, 'r12': True, 'p37': True}]

    for all_models in [all_models1, all_models2, all_models3]:
        for idx in range(len(all_models)):
            if debug:
                print('Testing synthesis of formula for model', all_models[idx])
            f = synthesize_for_model(frozendict(all_models[idx]))
            assert type(f) is Formula, 'Expected a formula, got ' + str(f)
            assert is_clause(f), str(f) + ' should be a clause'
            all_values = [False] * len(all_models)
            all_values[idx] = True
            for model,value in zip(all_models, all_values):
                assert evaluate(f, frozendict(model)) == value

def is_clause(f):
    if is_variable(f.root) or (f.root == '~' and is_variable(f.first.root)):
        return True
    return f.root == '&' and is_clause(f.first) and is_clause(f.second)

##def test_synthesize(debug=False):
##    all_models1 = [{'p': False}, {'p': True}]
##    value_lists1 = [(False, False), (False, True), (True, False), (True, True)]
##
##    all_models2 = [{'p': False, 'q': False},
##                   {'p': False, 'q': True},
##                   {'p': True,  'q': False},
##                   {'p': True,  'q': True}]
##    value_lists2 = [(True,  False, False, True),
##                    (True,  True,  True,  True),
##                    (False, False, False, False)]
##
##    all_models3 = [{'r1': False, 'r12': False, 'p37': False},
##                   {'r1': False, 'r12': False, 'p37': True},
##                   {'r1': False, 'r12': True, 'p37': False},
##                   {'r1': False, 'r12': True, 'p37': True},
##                   {'r1': True, 'r12': False, 'p37': False},
##                   {'r1': True, 'r12': False, 'p37': True},
##                   {'r1': True, 'r12': True, 'p37': False},
##                   {'r1': True, 'r12': True, 'p37': True}]
##    value_lists3 = [(True, False, True, True, False, True, False, True),
##                    (True, True, True, True, True, True, True, True),
##                    (False, False, False, False, False, False, False, False)]
##
##    for all_models,value_lists in [[all_models1, value_lists1],
##                                   [all_models2, value_lists2],
##                                   [all_models3, value_lists3]]:
##        all_models == [frozendict(model) for model in all_models]
##        for all_values in value_lists:
##            if debug:
##                print('Testing synthesis of formula for models', all_models,
##                      'with values', all_values)
##            f = synthesize(all_models, all_values)
##            assert type(f) is Formula, 'Expected a formula, got ' + str(f)
##            assert is_DNF(f), str(f) + ' should be a DNF'
##            for model,value in zip(all_models, all_values):
##                assert evaluate(f, model) == value, \
##                       str(f) + ' evaluates to ' + str(evaluate(f, model)) + \
##                       ' on ' + str(model)

def test_synthesize(debug=False):
    all_variables1 = ['p']
    all_models1 = [{'p': False}, {'p': True}]
    value_lists1 = [(False, False), (False, True), (True, False), (True, True)]

    all_variables2 = ['p', 'q']
    all_models2 = [{'p': False, 'q': False},
                   {'p': False, 'q': True},
                   {'p': True,  'q': False},
                   {'p': True,  'q': True}]
    value_lists2 = [(True,  False, False, True),
                    (True,  True,  True,  True),
                    (False, False, False, False)]

    all_variables3 = ['r1', 'r12', 'p37']
    all_models3 = [{'r1': False, 'r12': False, 'p37': False},
                   {'r1': False, 'r12': False, 'p37': True},
                   {'r1': False, 'r12': True, 'p37': False},
                   {'r1': False, 'r12': True, 'p37': True},
                   {'r1': True, 'r12': False, 'p37': False},
                   {'r1': True, 'r12': False, 'p37': True},
                   {'r1': True, 'r12': True, 'p37': False},
                   {'r1': True, 'r12': True, 'p37': True}]
    value_lists3 = [(True, False, True, True, False, True, False, True),
                    (True, True, True, True, True, True, True, True),
                    (False, False, False, False, False, False, False, False)]

    for all_variables, all_models,value_lists in [
            [all_variables1, all_models1, value_lists1],
            [all_variables2, all_models2, value_lists2],
            [all_variables3, all_models3, value_lists3]]:
        for all_values in value_lists:
            if debug:
                print('Testing synthesis of formula for variables',
                      all_variables, 'and model-values', all_values)
            formula = synthesize(all_variables, all_values)
            assert type(formula) is Formula, \
                   'Expected a formula, got ' + str(formula)
            assert is_DNF(formula), str(formula) + ' should be a DNF'
            assert formula.variables().issubset(set(all_variables))
            for model, value in zip(all_models, all_values):
                assert evaluate(formula, frozendict(model)) == value, \
                       str(formula) + ' does not evaluate to ' + str(value) + \
                       ' on ' + str(model)

def is_DNF(formula):
    return is_clause(formula) or \
           (formula.root == '|' and is_DNF(formula.first) and
            is_DNF(formula.second))

def test_evaluate_inference(debug=False):
    from propositions.proofs import InferenceRule

    # Test 1
    rule1 = InferenceRule([Formula.parse('p'), Formula.parse('q')],
                          Formula.parse('r'))
    for model in all_models(['p', 'q', 'r']):
        if debug:
            print('Testing evaluation of inference rule', rule1, 'in model',
                  model)
        assert evaluate_inference(rule1, frozendict(model)) == \
               (not model['p']) or (not model['q']) or model['r']

    # Test 2
    rule2 = InferenceRule([Formula.parse('(x|y)')],
                          Formula.parse('x'))
    for model in all_models(['x', 'y']):
        if debug:
            print('Testing evaluation of inference rule', rule2, 'in model',
                  model)
        assert evaluate_inference(rule2, frozendict(model)) == \
               (not model['y']) or model['x']

    # Test 3
    rule3 = InferenceRule([Formula.parse(s) for s in ['(p->q)', '(q->r)']],
                           Formula.parse('r'))
    for model in all_models(['p', 'q', 'r']):
        if debug:
            print('Testing evaluation of inference rule', rule3, 'in model',
                  model)
        assert evaluate_inference(rule3, frozendict(model)) == \
               (model['p'] and not model['q']) or \
               (model['q'] and not model['r']) or model['r']

def test_is_sound_inference(debug=False):
    from propositions.proofs import InferenceRule

    for assumptions,conclusion,tautological in [
            [[], '(~p|p)', True],
            [[], '(p|p)', False],
            [[], '(~p|q)', False],
            [['(~p|q)', 'p'], 'q', True],
            [['(p|q)', 'p'], 'q', False],
            [['(p|q)', '(~p|r)'], '(q|r)', True],
            [['(p->q)', '(q->r)'], 'r', False],
            [['(p->q)', '(q->r)'], '(p->r)', True],
            [['(x|y)'], '(y|x)', True],
            [['x'], '(x|y)', True],
            [['(x&y)'], 'x', True],
            [['x'], '(x&y)', False]]:
        rule = InferenceRule(
            [Formula.parse(assumption) for assumption in assumptions],
            Formula.parse(conclusion))
        if debug:
            print('Testing whether', rule, 'is sound')
        assert is_sound_inference(rule) == tautological

    for rule in [MP, I0, I1, D, I2, N, NI, NN, R,
                 A, NA1, NA2, O1, O2, NO, T, NF,
                 N_ALTERNATIVE, AE1, AE2, OE]:
        if debug:
            print('Testing that', rule, 'is sound')
        assert is_sound_inference(rule)

def test_evaluate_all_operators(debug=False):
    infix1 = '(p+q7)'
    models_values1 = [
        ({'p': True,  'q7': False}, True),
        ({'p': False, 'q7': False}, False),
        ({'p': True,  'q7': True},  False)
    ]
    infix2 = '~(p<->q7)'
    models_values2 = [
        ({'p': True,  'q7': False}, True),
        ({'p': False, 'q7': False}, False),
        ({'p': True,  'q7': True},  False)
    ]
    infix3 = '~((x-&x)-|(y-&y))'
    models_values3 = [
        ({'x': True,  'y': False}, True),
        ({'x': False,  'y': False}, True),
        ({'x': True,  'y': True}, False)
    ]
    for infix,models_values in [[infix1, models_values1],
                                [infix2, models_values2],
                                [infix3, models_values3]]:
        formula = Formula.parse(infix)
        for model,value in models_values:
            if debug:
                print('Testing evaluation of formula', formula, 'in model',
                      model)
            assert evaluate(formula, frozendict(model)) == value

def test_is_tautology_all_operators(debug=False):
    for infix,tautology in [['~(p-&q7)', False], ['(x<->~~x)', True],
                            ['(F-&T)',  True],  ['((y1+~y1)&T)', True],
                            ['(x-|x)',  False], ['((x-&y)<->(~x|~y))', True]]:
        formula = Formula.parse(infix)
        if debug:
            print('Testing whether', formula, 'is a tautology')
        assert is_tautology(formula) == tautology

def test_ex2(debug=False):
    test_evaluate(debug)
    test_all_models(debug)
    test_truth_values(debug)
    test_print_truth_table(debug)
    test_is_tautology(debug)
    test_is_contradiction(debug)
    test_is_satisfiable(debug)
    test_synthesize_for_model(debug)
    test_synthesize(debug)

def test_ex3(debug=False):
    assert is_binary('+'), 'Change is_binary() before testing Chapter 3 tasks.'
    test_evaluate_all_operators(debug)
    test_is_tautology_all_operators(debug)

def test_ex4(debug=False):
    test_evaluate_inference(debug)
    test_is_sound_inference(debug)
    
def test_all(debug=False):
    test_ex2(debug)
    test_ex3(debug)
    test_ex4(debug)
