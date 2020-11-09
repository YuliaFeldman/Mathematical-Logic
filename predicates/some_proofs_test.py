# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/some_proofs_test.py

"""Tests for the predicates.some_proofs module."""

from predicates.some_proofs import *

def test_lovers_proof(debug=False):
    proof = lovers_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[Ey[Loves(x,y)]]')),
         Schema(Formula.parse('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'))})
    assert str(proof.conclusion) == 'Ax[Az[Loves(z,x)]]'
    assert proof.is_valid()

def test_homework_proof(debug=False):
    proof = homework_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('~Ex[(Homework(x)&Fun(x))]')),
         Schema(Formula.parse('Ex[(Homework(x)&Reading(x))]'))})
    assert str(proof.conclusion) == 'Ex[(Reading(x)&~Fun(x))]'
    assert proof.is_valid()

def test_unique_zero_proof(debug=False):
    proof = unique_zero_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) for a in GROUP_AXIOMS},
        {Schema(Formula.parse('plus(a,c)=a'))})
    assert str(proof.conclusion) == 'c=0'
    assert proof.is_valid()

def test_multiply_zero_proof(debug=False):
    proof = multiply_zero_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) for a in FIELD_AXIOMS})
    assert str(proof.conclusion) == 'times(0,x)=0'
    assert proof.is_valid()

def test_peano_zero_proof(debug=False):
    proof = peano_zero_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) if type(a) is str else a
         for a in PEANO_AXIOMS})
    assert str(proof.conclusion) == 'plus(0,x)=x'
    assert proof.is_valid()

def test_russell_paradox_proof(debug=False):
    proof = russell_paradox_proof(debug)
    assert proof.assumptions == Prover.AXIOMS.union({COMPREHENSION_AXIOM})
    assert str(proof.conclusion) == '(z=z&~z=z)'
    assert proof.is_valid()

def test_not_exists_not_implies_all_proof(debug=False):
    for formula,variable,equivalence in [
        ('R(x)', 'x', '(~Ex[~R(x)]->Ax[R(x)])'),
        ('Q(y)', 'y', '(~Ey[~Q(y)]->Ay[Q(y)])')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing not_exists_not_implies_all_proof to prove',
                  equivalence)
        proof = not_exists_not_implies_all_proof(formula, variable, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_exists_not_implies_not_all_proof(debug=False):
    for formula,variable,equivalence in [
        ('R(x)', 'x', '(Ex[~R(x)]->~Ax[R(x)])'),
        ('Q(y)', 'y', '(Ey[~Q(y)]->~Ay[Q(y)])')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing exists_not_implies_not_all_proof to prove',
                  equivalence)
        proof = exists_not_implies_not_all_proof(formula, variable, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_not_all_iff_exists_not_proof(debug=False):
    for formula,variable,equivalence in [
        ('R(x)', 'x', '((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
        ('Q(y)', 'y', '((~Ay[Q(y)]->Ey[~Q(y)])&(Ey[~Q(y)]->~Ay[Q(y)]))')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing not_all_iff_exists_not_proof to prove',
                  equivalence)
        proof = not_all_iff_exists_not_proof(formula, variable, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_ex10(debug=False):
    test_lovers_proof(debug)
    test_homework_proof(debug)
    test_unique_zero_proof(debug)
    test_multiply_zero_proof(debug)
    test_peano_zero_proof(debug)
    test_russell_paradox_proof(debug)

def test_ex11_opt(debug=False):
    test_not_exists_not_implies_all_proof(debug)
    test_exists_not_implies_not_all_proof(debug)
    test_not_all_iff_exists_not_proof(debug)

def test_all(debug=False):
    test_ex10(debug)
    test_ex11_opt(debug)
