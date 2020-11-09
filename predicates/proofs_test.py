# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/proofs_test.py

"""Tests for the predicates.proofs module."""

from predicates.syntax import *
from predicates.proofs import *

def test_instantiate_helper(debug=False):
    for formula,templates,constant_and_variable_instantiation_map,\
        relations_instantiation_map,instance in [
            ('R(c)', {'c'}, {'c': Term('9')}, {},  'R(9)'),
            ('~R(cd)', {'cd'}, {'cd': Term('9')}, {},  '~R(9)'),
            ('(R(0)&R(x))', {'R'}, {}, {'R': Formula.parse('_=1')},
             '(0=1&x=1)'),
            ('(RQ(0)|RQ(x))', {'RQ'}, {}, {'RQ': Formula.parse('1=1')},
             '(1=1|1=1)'),
            ('(R(0)->Q())', {'R'}, {},
             {'R': Formula.parse('_=1'), 'Q': Formula.parse('1=1')},
             '(0=1->1=1)'),
            ('(Ax[R(x)]->R(c))', {'c', 'R'}, {'c': Term('9')},
             {'R': Formula.parse('(Q(y)|_=0)')},
             '(Ax[(Q(y)|x=0)]->(Q(y)|9=0))'),
            ('((R(0)&Az[(R(z)->R(s(z)))])->Az[R(z)])', {'R'}, {},
             {'R': Formula.parse('plus(x,_)=plus(_,x)')},
             '((plus(x,0)=plus(0,x)&Az[(plus(x,z)=plus(z,x)->plus(x,s(z))=' +
             'plus(s(z),x))])->Az[plus(x,z)=plus(z,x)])'),
            ('Ax[R(x)]', {'R'}, {}, {'R': Formula.parse('_=1')},
             'Ax[x=1]'),
            ('Ax[R(x)]', {'R', 'x'}, {'x': Term('z')},
             {'R': Formula.parse('_=x')}, 'Az[z=x]'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {}, {}, '(Ax[R(x)]->R(c))'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'},
             {'x': Term('z'), 'y': Term('z')}, {}, '(Az[R(z)]->Az[R(z)])'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'},
             {'x': Term('y'), 'y': Term('y')}, {}, '(Ay[R(y)]->Ay[R(y)])'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'},
             {'x': Term('y'), 'y': Term('x')}, {}, '(Ay[R(y)]->Ax[R(x)])'),
            ('(Axy[R(xy)]->R(c))', {'xy', 'c', 'R'},
             {'xy': Term('z'), 'c': Term('z')},
             {'R': Formula.parse('Ay[(L(x,y)->L(_,x))]')},
             '(Az[Ay[(L(x,y)->L(z,x))]]->Ay[(L(x,y)->L(z,x))])')]:
        formula = Formula.parse(formula)
        schema = Schema(formula, frozenset(templates))
        if debug:
            print('Substituting constant and variable instantiation map',
                  constant_and_variable_instantiation_map,
                  'and relations instantiation map',
                  relations_instantiation_map,
                  'in schema', schema, '...')
        result = schema._instantiate_helper(
            formula, frozendict(constant_and_variable_instantiation_map),
            frozendict(relations_instantiation_map))
        if debug:
            print('... yields', result)
        assert str(result) == instance

    for formula,templates,constant_and_variable_instantiation_map,\
        relations_instantiation_map,variable_name,relation_name in [
            ('Ax[R(0)]', {'R'}, {}, {'R': Formula.parse('x=1')}, 'x', 'R'),
            ('Ax[Q(0)]', {'Q', 'x'}, {'x': Term('z')},
             {'Q':Formula.parse('z=1')}, 'z', 'Q'),
            ('(Ax[R(x)]->R(c))', {'R','x','c'}, {},
             {'R':Formula.parse('Ex[_=7]')}, 'x', 'R')]:
        formula = Formula.parse(formula)
        schema = Schema(formula, frozenset(templates))
        if debug:
            print('Substituting constant and variable instantiation map',
                  constant_and_variable_instantiation_map,
                  'and relations instantiation map',
                  relations_instantiation_map,
                  'in schema', schema, '...')
        reached = False
        try:
            result = schema._instantiate_helper(
                formula, frozendict(constant_and_variable_instantiation_map),
                frozendict(relations_instantiation_map))
            reached = True
        except Schema.BoundVariableError as e:
            if debug:
                print('Threw a BoundVariableError as expected')
            assert e.variable_name == variable_name
            assert e.relation_name == relation_name
        except Exception as e:
            if debug:
                print('Threw an exception as expected, though not a '
                      'BoundVariableError, but instead: ' + str(e))
        assert not reached, 'Expected exception'

def test_instantiate(debug=False):
    for formula,templates,instantiation_map,instance in [
            ('R(c)', {'c'}, {'c':Term('9')}, 'R(9)'),
            ('~R(cd)', {'cd'}, {'cd': Term('9')},  '~R(9)'),
            ('(R(0)&R(x))', {'R'}, {'R':Formula.parse('_=1')},
             '(0=1&x=1)'),
            ('(R(0)|R(x))', {'R'}, {'R':Formula.parse('1=1')},
             '(1=1|1=1)'),
            ('(R(0)->Q())', {'R', 'Q'},
             {'R':Formula.parse('_=1'), 'Q':Formula.parse('1=1')},
             '(0=1->1=1)'),
            ('(Ax[R(x)]->R(c))', {'c', 'R'},
             {'R':Formula.parse('(Q(y)|_=0)'), 'c':Term('9')},
             '(Ax[(Q(y)|x=0)]->(Q(y)|9=0))'),
            ('((R(0)&Az[(R(z)->R(s(z)))])->Az[R(z)])', {'R'},
             {'R':Formula.parse('plus(x,_)=plus(_,x)')},
             '((plus(x,0)=plus(0,x)&Az[(plus(x,z)=plus(z,x)->plus(x,s(z))=' +
             'plus(s(z),x))])->Az[plus(x,z)=plus(z,x)])'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R':Formula.parse('Q(_)')},
             '(Ay[Q(y)]->Q(0))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R':Formula.parse('Q(v)')},
             '(Ay[Q(v)]->Q(v))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term.parse('f(g(a),g(a))'), 'x':'x',
              'R':Formula.parse('(_=0|R(_))')},
             '(Ax[(x=0|R(x))]->(f(g(a),g(a))=0|R(f(g(a),g(a)))))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {}, '(Ax[R(x)]->R(c))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'Q':Formula.parse('_=0')},
             None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R':Formula.parse('Q(0)'), 'a':Term('b')}, None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'c':Term.parse('f(x)')},
             '(Ax[R(x)]->R(f(x)))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'c':Term('x'), 'x':'z'},
             '(Az[R(z)]->R(x))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R':Formula.parse('Q(_,z)')}, '(Ax[Q(x,z)]->Q(c,z))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R':Formula.parse('Q(_,x)')}, None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'x':'z', 'R':Formula.parse('Q(_,x)')},
             '(Az[Q(z,x)]->Q(c,x))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('z'), 'R':Formula.parse('Q(_,z)')},
             '(Ax[Q(x,z)]->Q(z,z))'),
            ('(Ax[R(x)]->R(c))', {'x', 'c', 'R'},
             {'x':'z', 'c':Term('z'),
              'R':Formula.parse('Ay[(L(x,y)->L(_,x))]')},
             '(Az[Ay[(L(x,y)->L(z,x))]]->Ay[(L(x,y)->L(z,x))])'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'}, {'x':'z', 'y':'z'},
             '(Az[R(z)]->Az[R(z)])'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'}, {'x':'y', 'y':'y'},
             '(Ay[R(y)]->Ay[R(y)])'),
            ('(Ax[R(x)]->Ay[R(y)])', {'x', 'y'}, {'x':'y', 'y':'x'},
             '(Ay[R(y)]->Ax[R(x)])'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c1':Term.parse('f(x)'), 'R':Formula.parse('_=c')},
             '(f(x)=c2->(f(x)=c->c2=c))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c2':Term('c1'), 'c1':Term('c2')}, '(c2=c1->(R(c2)->R(c1)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'R':Formula.parse('R(c1,c2,_)')},
             '(c1=c2->(R(c1,c2,c1)->R(c1,c2,c2)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c1':Term('c2'), 'c2':Term('c1'),
              'R':Formula.parse('R(c1,c2,_)')},
             '(c2=c1->(R(c1,c2,c2)->R(c1,c2,c1)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'R':Formula.parse('(Q(_)&Av[S(v)])')},
             '(c1=c2->((Q(c1)&Av[S(v)])->(Q(c2)&Av[S(v)])))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('v=0'), 'R':Formula.parse('S(_)')},
             '(Ax[(v=0->S(x))]->(v=0->Ax[S(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('v=0'), 'R':Formula.parse('S(_)'),
              'x':'z'},
             '(Az[(v=0->S(z))]->(v=0->Az[S(z)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('z=0')},
             '(Ax[(z=0->R(x))]->(z=0->Ax[R(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('x=0')}, None),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('Ax[x=0]')},
             '(Ax[(Ax[x=0]->R(x))]->(Ax[x=0]->Ax[R(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('x=0'), 'x':'z'},
             '(Az[(x=0->R(z))]->(x=0->Az[R(z)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('z=0'), 'x':'z'}, None),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q':Formula.parse('Az[z=0]'), 'x':'z'},
             '(Az[(Az[z=0]->R(z))]->(Az[z=0]->Az[R(z)]))'),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'RRR':Formula.parse('_=yyy'), 'yyy':'xxx'},
             '(Axxx[xxx=yyy]->Exxx[QQQ(xxx)])'),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'QQQ':Formula.parse('_=0')}, None),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'QQQ':Formula.parse('RRR(_)')}, None),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'}, {'xxx':'z'},
             None),
            ('(Ax[R(x)]->R(c))', {'R','x','c'},
             {'R':Formula.parse('Ex[_=7]')}, None)
            ]:
        schema = Schema(Formula.parse(formula), frozenset(templates))
        if debug:
            print('Substituting instantiation map', instantiation_map,
                  'in schema', schema, '...')
        result = schema.instantiate(frozendict(instantiation_map))
        if debug:
            print('... yields', result)
        if instance is None:
            assert result is None
        else:
            assert str(result) == instance

def test_assumption_line_is_valid(debug=False):
    for assumption,templates,instantiation_map,formula,validity in [
            ('u=0', {'u'}, {'u': 'x'}, 'x=0', True),
            ('(u=0->v=1)', {'u', 'v'}, {'u': 'x', 'v': 'y'},
             '(x=0->y=1)', True),
            ('Ev[u=f(v)]', {'v'}, {'v': 'x'}, 'Ex[u=f(x)]', True),
            ('u=0', {'u'}, {'u': 'x'}, 'y=0', False),
            ('Av[u=v]', {'u'}, {'u': 'x'}, 'Av[u=v]', False),
            ('Av[u=v]', {'u'}, {'u': 'x'}, 'Ax[u=x]', False),
            ('Ax[(Q(z)->R(x))]', {'Q'}, {'Q': Formula.parse('x=_')},
             'Ax[(x=z->R(x))]', False)]:
        assumption = Schema(Formula.parse(assumption), templates)
        line = Proof.AssumptionLine(Formula.parse(formula), assumption,
                                    instantiation_map)
        if debug:
            print("Verifying validity of assumption line '" + str(line) +
                  "' given assumption " + str(assumption))
        result = line.is_valid(frozenset({assumption}), [line], 0)
        if debug:
            print('... yields', result)
        assert result == validity

    # Test foreign assumption
    assumption = Schema(Formula.parse('u=1'), {'u'})
    formula = Formula.parse('x=0')
    line = Proof.AssumptionLine(formula,
                                Schema(Formula.parse('u=0'), {'u'}),
                                {'u': 'x'})
    if debug:
        print("Verifying validity of assumption line '" + str(line) +
              "' given assumption " + str(assumption))
    result = line.is_valid(frozenset({assumption}), [line], 0)
    if debug:
        print('... yields', result)
    assert not result

def test_mp_line_is_valid(debug=False):
    # Test valid line
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    lines = [Proof.AssumptionLine(Formula.parse('x=0'), assumption1,
                                  {'u': 'x'}),
             Proof.AssumptionLine(Formula.parse('(x=0->y=1)'), assumption2,
                                  {'u': 'x', 'v': 'y'}),
             Proof.MPLine(Formula.parse('y=1'), 0, 1)]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 2
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test valid line reversed order assumption
    assumption1 = Schema(Formula.parse('(c=1->d=2)'), {'c', 'd'})
    assumption2 = Schema(Formula.parse('c=3'), {'c'})
    lines = [Proof.AssumptionLine(Formula.parse('(f(x)=0->g(y)=1)'),
                                  assumption1,
                                  {'c': Term.parse('f(x)'),
                                   'd': Term.parse('g(y)')}),
             Proof.AssumptionLine(Formula.parse('f(x)=0'), assumption2,
                                  {'c': Term.parse('f(x)')}),
             Proof.MPLine(Formula.parse('g(y)=1'), 1, 0)]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 2
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test valid line with quantifier
    assumption1 = Schema(Formula.parse('(c=0->d=1)'), {'c', 'd'})
    assumption2 = Schema(Formula.parse('c=0'), {'c'})
    lines = [Proof.AssumptionLine(Formula.parse('(Ax[f(x)=0]->Ey[f(y)=1])'),
                                  assumption1,
                                  {'c': Term.parse('f(x)'),
                                   'd': Term.parse('f(y)')}),
             Proof.AssumptionLine(Formula.parse('Ax[f(x)=0]'),
                                  assumption2, {'c': Term.parse('f(x)')}),
             Proof.MPLine(Formula.parse('Ey[f(y)=1]'), 1, 0)]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 2
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test invalid line - type 1
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=1->v=1)'), {'u', 'v'})
    lines = [Proof.AssumptionLine(Formula.parse('x=0'), assumption1,
                                  {'u': 'x'}),
             Proof.AssumptionLine(Formula.parse('(x=1->y=1)'),
                                  assumption2, {'u': 'x', 'v': 'y'}),
             Proof.MPLine(Formula.parse('y=1'), 0, 1)]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 2
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert not result

    # Test invalid line - type 2
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    lines = [Proof.AssumptionLine(Formula.parse('x=0'), assumption1,
                                  {'u': 'x'}),
             Proof.AssumptionLine(Formula.parse('(x=0->y=1)'), assumption2,
                                  {'u': 'x', 'v': 'y'}),
             Proof.MPLine(Formula.parse('y=0'), 0, 1)]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 2
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert not result

    # Test pointing to lines that appear after the conclusion
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    lines = [Proof.AssumptionLine(Formula.parse('x=0'), assumption1,
                                  {'u': 'x'}),
             Proof.MPLine(Formula.parse('y=1'), 0, 2),
             Proof.AssumptionLine(Formula.parse('(x=0->y=1)'), assumption2,
                                  {'u': 'x', 'v': 'y'})]
    proof = Proof({assumption1, assumption2}, lines[-1].formula, lines)
    checked_line = 1
    if debug:
        print("Verifying validity of MP line '" + str(lines[checked_line]) +
              "' in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert not result

def test_ug_line_is_valid(debug=False):
    for assumption, templates, formula, validity in [
            ('x=0', {'x'}, 'Ax[x=0]', True),
            ('x=0', {'x'}, 'Ay[x=0]', True),
            ('Ax[x=0]', set(), 'Ax[Ax[x=0]]', True),
            ('(x=0&y=0)', {'x', 'y'}, 'Ax[(x=0&y=0)]', True),
            ('R(c)', {'c'}, 'Axyz[R(c)]', True),
            ('x=0', {'x'}, 'Ex[x=0]', False),
            ('x=0', {'x'}, 'Ax[z=0]', False),
            ('(x=0&y=0)', {'x', 'y'}, '(Ax[x=0]&y=0)', False)]:
        assumption = Schema(Formula.parse(assumption), templates)
        formula = Formula.parse(formula)
        lines = [Proof.AssumptionLine(assumption.formula, assumption, {}),
                 Proof.UGLine(formula, 0)]
        proof = Proof({assumption}, formula, lines)
        checked_line = 1
        if debug:
            print("Verifying validity of UG line '" + str(lines[checked_line]) +
                  " in proof:\n" + str(proof))
        result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                              checked_line)
        if debug:
            print('... yields', result)
        assert result == validity

    # Test pointing to lines that appear after the conclusion
    assumption = Schema(Formula.parse('x=0'), {'x'})
    formula = Formula.parse('Ax[x=0]')
    lines = [Proof.UGLine(formula, 1),
             Proof.AssumptionLine(assumption.formula, assumption, {})]
    proof = Proof({assumption}, formula, lines)
    checked_line = 0
    if debug:
        print("Verifying validity of UG line '" + str(lines[checked_line]) +
              " in proof:\n" + str(proof))
    result = lines[checked_line].is_valid(proof.assumptions, proof.lines,
                                          checked_line)
    if debug:
        print('... yields', result)
    assert not result

def test_tautology_line_is_valid(debug=False):
    for formula,validity in [
            ('(R(c)|~R(c))', True),
            ('(x=0->x=0)', True),
            ('(((R(x)->Q(y))&(Q(y)->S(z)))->(R(x)->S(z)))', True),
            ('(Ex[x=0]->Ex[x=0])', True),
            ('x=0', False),
            ('x=x', False),
            ('Ax[(R(0)|~R(0))]', False)]:
        line = Proof.TautologyLine(Formula.parse(formula))
        if debug:
            print("Verifying validity of tautology line '" + str(line) + "'")
        result = line.is_valid(frozenset(), [line], 0)
        if debug:
            print('... yields', result)
        assert result == validity

def test_is_valid(debug=False):
    assumptions = []
    conclusion = Formula.parse('(R(0)|~R(0))')
    lines = []
    lines.append(Proof.TautologyLine(Formula.parse('(R(0)|R(0))')))
    proof = Proof(assumptions, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert not proof.lines[0].is_valid(proof.assumptions, proof.lines, 0)
    assert not proof.is_valid()
    lines[0] = Proof.TautologyLine(Formula.parse('(R(0)->R(0))'))
    proof = Proof(assumptions, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.lines[0].is_valid(proof.assumptions, proof.lines, 0)
    assert not proof.is_valid()
    lines[0] = Proof.TautologyLine(conclusion)
    proof = Proof(assumptions, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.lines[0].is_valid(proof.assumptions, proof.lines, 0)
    assert proof.is_valid()

    assumption1 = Schema(Formula.parse('R(0)'))
    assumption2 = Schema(Formula.parse('(R(0)->Q(1))'))
    conclusion = Formula.parse('Q(1)')
    lines = [Proof.AssumptionLine(assumption1.formula, assumption1, {}),
             Proof.AssumptionLine(assumption2.formula, assumption2, {}),
             Proof.MPLine(conclusion, 0, 1)]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.is_valid()


    assumption = Schema(Formula.parse('R(x)'))
    conclusion = Formula.parse('Ax[R(x)]')
    lines = [Proof.AssumptionLine(assumption.formula, assumption, {}),
             Proof.UGLine(conclusion, 0)]
    proof = Proof({assumption}, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.is_valid()

def test_axiom_specialization_map_to_schema_instantiation_map(debug=False):
    propositional_specialization_map = {
        'p': PropositionalFormula.parse('(z1->z2)'),
        'q': PropositionalFormula.parse('z1'),
        'r': PropositionalFormula.parse('~(z3&z2)')}
    substitution_map = {'z1': Formula.parse('Ax[x=5]'),
                        'z2': Formula.parse('M()'),
                        'z3': Formula.parse('z2=5')}
    expected = {'P': Formula.parse('(Ax[x=5]->M())'),
                'Q': Formula.parse('Ax[x=5]'),
                'R': Formula.parse('~(z2=5&M())')}
    if debug:
        print('Testing conversion of propositional specialization map',
              propositional_specialization_map,
              'to instantiation_map via substitution map', substitution_map)
    instantiation_map = axiom_specialization_map_to_schema_instantiation_map(
        frozendict(propositional_specialization_map),
        frozendict(substitution_map))
    assert instantiation_map == expected, instantiation_map

def test_prove_from_skeleton_proof(debug=False):
    from propositions.tautology import prove_tautology

    for formula,skeleton,substitution_map in [
        ('(R(c)->R(c))', '(z23->z23)', {'z23':Formula.parse('R(c)')})
        ,
        ('(x=0->x=0)', '(z24->z24)', {'z24':Formula.parse('x=0')}),
        ('(Ex[x=0]->Ex[x=0])', '(z25->z25)', {'z25':Formula.parse('Ex[x=0]')}),
        ('((~y=1->~x=1)->(x=1->y=1))', '((~z26->~z27)->(z27->z26))',
         {'z26':Formula.parse('y=1'), 'z27':Formula.parse('x=1')}),
        ('(~~Ex[y=2]->Ex[y=2])', '(~~z28->z28)',
         {'z28':Formula.parse('Ex[y=2]')}),
        ('(Ex[Ey[x=y]]->~~Ex[Ey[x=y]])', '(z29->~~z29)',
         {'z29':Formula.parse('Ex[Ey[x=y]]')}),
        ('((~Ex[(x=2->x=3)]->~R(y,4))->((Ex[(x=2->x=3)]->~R(y,4))->~R(y,4)))',
         '((~z30->~z31)->((z30->~z31)->~z31))',
         {'z30':Formula.parse('Ex[(x=2->x=3)]'),
          'z31':Formula.parse('R(y,4)')}),
        ('((Ey[~x=y]->(y=3->y=74))->(y=3->(Ey[~x=y]->y=74)))',
         '((z32->(z33->z34))->(z33->(z32->z34)))',
         {'z32':Formula.parse('Ey[~x=y]'), 'z33':Formula.parse('y=3'),
          'z34':Formula.parse('y=74')}),
        ('(~~~~Q()->~~Q())', '(~~~~z35->~~z35)', {'z35':Formula.parse('Q()')})
    ]:
        if debug:
            print('Testing proving', formula, 'from proof of', skeleton)
        formula = Formula.parse(formula)
        skeleton = PropositionalFormula.parse(skeleton)
        skeleton_proof = prove_tautology(skeleton)
        assert skeleton_proof.is_valid(), 'Bug in prove_tautology!'
        proof = prove_from_skeleton_proof(formula, skeleton_proof,
                                          frozendict(substitution_map))
        assert proof.assumptions == PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS
        assert proof.conclusion == formula
        assert proof.is_valid()

def test_prove_tautology(debug=False):
    for tautology in [
            '(R(c)->R(c))', '(x=0->x=0)', '(Ex[x=0]->Ex[x=0])',
            '((~y=1->~x=1)->(x=1->y=1))', '(~~Ex[y=2]->Ex[y=2])',
            '(Ex[Ey[x=y]]->~~Ex[Ey[x=y]])',
            '((~Ex[(x=2->x=3)]->~R(y,4))->' +
            '((Ex[(x=2->x=3)]->~R(y,4))->~R(y,4)))',
            '((Ey[~x=y]->(y=3->y=74))->(y=3->(Ey[~x=y]->y=74)))',
            '(~~~~Q()->~~Q())']:
        if debug:
            print('Testing proving the tautology', tautology)
        tautology = Formula.parse(tautology)
        proof = prove_tautology(tautology)
        assert proof.assumptions == PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS
        assert proof.conclusion == tautology
        for line in proof.lines:
            assert type(line) in {Proof.AssumptionLine, Proof.MPLine}
        assert proof.is_valid()

def test_ex9(debug=False):
    test_instantiate_helper(debug)
    test_instantiate(debug)
    test_assumption_line_is_valid(debug)
    test_mp_line_is_valid(debug)
    test_ug_line_is_valid(debug)
    test_tautology_line_is_valid(debug)
    test_is_valid(debug)
    test_axiom_specialization_map_to_schema_instantiation_map(debug)
    test_prove_from_skeleton_proof(debug)
    test_prove_tautology(debug)

def test_all(debug=False):
    test_ex9(debug)
