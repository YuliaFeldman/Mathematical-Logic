# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prover_test.py

"""Tests for the predicates.prover module."""

from predicates.some_proofs import *

def test_prover_basic(debug=False):
    proof = syllogism_proof(debug)
    assert proof.conclusion == Formula.parse('Mortal(aristotle)')
    assert proof.is_valid()

    # Partial run - verifies all steps until stopped
    right_neutral_proof(True, True, True, True, debug)

def test_add_universal_instantiation(debug=False):
    proof = syllogism_proof_with_universal_instantiation(debug)
    assert str(proof.conclusion) == 'Mortal(aristotle)'
    assert proof.is_valid()

    # With a different variable name
    prover = Prover({'Ay[(Man(y)->Mortal(y))]', 'Man(aristotle)'}, debug)
    step1 = prover.add_assumption('Ay[(Man(y)->Mortal(y))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    proof = prover.qed()
    assert str(proof.conclusion) == 'Mortal(aristotle)'
    assert proof.is_valid()

    # With functions
    prover = Prover({'Ax[x=plus(0,x)]'}, debug)
    step1 = prover.add_assumption('Ax[x=plus(0,x)]')
    step2 = prover.add_universal_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', step1, 'plus(x,0)')
    proof = prover.qed()
    assert str(proof.conclusion) == 'plus(x,0)=plus(0,plus(x,0))'
    assert proof.is_valid()
    
    proof = syllogism_all_all_proof(debug)
    assert str(proof.conclusion) == 'Ax[(Greek(x)->Mortal(x))]'
    assert proof.is_valid()

def test_add_tautological_implication(debug=False):
    proof = syllogism_all_all_proof_with_tautological_implication(debug)
    assert str(proof.conclusion) == 'Ax[(Greek(x)->Mortal(x))]'
    assert proof.is_valid()

    proof = syllogism_all_exists_proof()
    assert str(proof.conclusion) == 'Ex[Mortal(x)]'
    assert proof.is_valid()

def test_add_existential_derivation(debug=False):
    proof = syllogism_all_exists_proof_with_existential_derivation(debug)
    assert str(proof.conclusion) == 'Ex[Mortal(x)]'
    assert proof.is_valid()

    # With a different variable name
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ey[Man(y)]'}, debug)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ey[Man(y)]')
    step3 = prover.add_universal_instantiation(
        '(Man(y)->Mortal(y))', step1, 'y')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(y)->Ey[Mortal(y)])', Prover.EI,
        {'R':'Mortal(_)', 'x':'y', 'c':'y'})
    step5 = prover.add_tautological_implication(
        '(Man(y)->Ey[Mortal(y)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ey[Mortal(y)]', step2, step5)
    proof = prover.qed()
    assert str(proof.conclusion) == 'Ey[Mortal(y)]'
    assert proof.is_valid()

    # With an unquantified consequent
    prover = Prover({'Ax[(Man(x)->HumanityAlive())]', 'Ey[Man(y)]'}, debug)
    step1 = prover.add_assumption('Ax[(Man(x)->HumanityAlive())]')
    step2 = prover.add_universal_instantiation(
        '(Man(y)->HumanityAlive())', step1, 'y')
    step3 = prover.add_assumption('Ey[Man(y)]')
    step4 = prover.add_existential_derivation('HumanityAlive()', step3, step2)
    proof = prover.qed()
    assert str(proof.conclusion) == 'HumanityAlive()'
    assert proof.is_valid()

def test_add_flipped_equality(debug=False):
    # Partial run - stop before first add_free_instantiation
    proof = right_neutral_proof(False, True, True, True, debug)
    assert str(proof.conclusion) == 'plus(x,plus(y,z))=plus(plus(x,y),z)'
    assert proof.is_valid()
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(proof, 'x=plus(0,x)')
    assert _contains_line_with_formula(proof, '0=plus(minus(x),x)')
    assert _contains_line_with_formula(
        proof, 'plus(x,plus(y,z))=plus(plus(x,y),z)')

def test_add_free_instantiation(debug=False):
    # Partial run - stop before first add_substituted_equality
    proof = right_neutral_proof(False, False, True, True, debug)    
    assert str(proof.conclusion) == 'plus(0,plus(x,0))=plus(plus(0,x),0)'
    assert proof.is_valid()
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(
        proof, '0=plus(minus(minus(x)),minus(x))')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))')
    assert _contains_line_with_formula(proof, 'plus(0,0)=0')
    assert _contains_line_with_formula(proof, 'plus(x,0)=plus(0,plus(x,0))')
    assert _contains_line_with_formula(
        proof, 'plus(0,plus(x,0))=plus(plus(0,x),0)')

def test_add_substituted_equality(debug=False):
    # Partial run - stop before first add_chained_equality
    proof = right_neutral_proof(False, False, False, True, debug)
    assert str(proof.conclusion) == \
           'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)'
    assert proof.is_valid()
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(
        proof,
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)')
    assert _contains_line_with_formula(
        proof, 'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)')
    assert _contains_line_with_formula(
        proof, 'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))')
    assert _contains_line_with_formula(
        proof, 'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)')

def test_add_chained_equality(debug=False):
    proof = right_neutral_proof(False, False, False, False, debug)
    assert str(proof.conclusion) == 'plus(x,0)=x'
    assert proof.is_valid()

def _contains_line_with_formula(proof, formula):
    for line in proof.lines:
        if str(line.formula) == formula:
            return True
    return False

def test_ex10(debug=False):
    test_prover_basic(debug)
    test_add_universal_instantiation(debug)
    test_add_tautological_implication(debug)
    test_add_existential_derivation(debug)
    test_add_flipped_equality(debug)
    test_add_free_instantiation(debug)
    test_add_substituted_equality(debug)
    test_add_chained_equality(debug)

def test_all(debug=False):
    test_ex10(debug)
