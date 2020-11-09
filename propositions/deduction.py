# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from copy import  deepcopy


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    rules = []
    for rule in antecedent_proof.rules:
        rules.append(rule)
    rules.append(conditional)
    rules.append(MP)
    rules = set(rules)

    statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)

    lines = []
    for line in antecedent_proof.lines:
        lines.append(line)

    formula = Formula('->', antecedent_proof.statement.conclusion, consequent)
    specialization_map = InferenceRule.formula_specialization_map(conditional.conclusion,
                                                                  formula)
    new_formula = conditional.conclusion.substitute_variables(specialization_map)
    new_line1 = Proof.Line(new_formula, conditional, [])
    lines.append(new_line1)
    new_line2 = Proof.Line(consequent, MP, [len(lines)-2, len(lines)-1])
    lines.append(new_line2)

    return Proof(statement, rules, lines)


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)

    # Task 5.3b

    temp_consequent = Formula('->', antecedent2_proof.statement.conclusion, consequent)

    temp_proof1 = prove_corollary(antecedent1_proof, temp_consequent, double_conditional)

    temp_conditional_rule = InferenceRule([], temp_consequent)
    temp_proof_2 = prove_corollary(antecedent2_proof, consequent, temp_conditional_rule)

    shift_size = len(temp_proof1.lines)
    lines = []
    for line in temp_proof1.lines:
        lines.append(line)

    for line in temp_proof_2.lines:

        if not line.is_assumption():

            if line.rule not in temp_proof1.rules:
                new_line = temp_proof1.lines[len(temp_proof1.lines)-1]
            else:
                assumptions_of_line = [assump + shift_size for assump in line.assumptions]
                new_line = Proof.Line(line.formula, line.rule, assumptions_of_line)
        else:
            new_line = Proof.Line(line.formula, line.rule)
        lines.append(new_line)

    new_statement = InferenceRule(antecedent1_proof.statement.assumptions, consequent)
    p = Proof(new_statement, temp_proof1.rules, lines)

    #print("\nFirst proof given: \n" + str(antecedent1_proof))
    #print("____________________________________________")
    #print("Second proof given: \n" + str(antecedent2_proof))
    #print("____________________________________________")
    #print("Inference rule given: \n" + str(double_conditional))
    #print("____________________________________________")
    #print("Consequent formula given: \n" + str(consequent))
    #print("____________________________________________")
    #print("temp_proof_1:\n " + str(temp_proof1))
    #print("____________________________________________")
    #print("temp_proof_2:\n " + str(temp_proof_2))
    #print("____________________________________________")
    #print("temp_consequent:\n " + str(temp_consequent))
    #print("____________________________________________")
    #print("Final proof:\n"+ str(p))
    #print("\n*********************************************************************************")
    return p


def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4

    antecedent = proof.statement.assumptions[len(proof.statement.assumptions)-1]
    consequent = proof.statement.conclusion
    conclusion = Formula('->', antecedent, consequent)
    assumptions = proof.statement.assumptions[:len(proof.statement.assumptions) - 1]
    statement = InferenceRule(assumptions, conclusion)

    lines = []
    temp = [0]*len(proof.lines)
    i = 0
    for line in proof.lines:

        if line.formula == antecedent:
            formula = Formula('->', antecedent, line.formula)
            lines.append(Proof.Line(formula, I0, []))

        elif line.is_assumption():
            lines.append(line)
            temp_formula_2 = Formula('->', line.formula, Formula('->', antecedent, line.formula))
            lines.append(Proof.Line(temp_formula_2, I1, []))
            formula = Formula('->', antecedent, line.formula)
            lines.append(Proof.Line(formula, MP, [len(lines)-2, len(lines)-1]))

        elif not line.is_assumption():
            if len(line.assumptions) == 0:
                lines.append(line)
                temp_formula_1 = Formula('->', antecedent, line.formula)
                temp_formula_2 = Formula('->', line.formula, temp_formula_1)
                lines.append(Proof.Line(temp_formula_2, I1, []))
                lines.append(Proof.Line(temp_formula_1, MP, [len(lines)-2, len(lines)-1]))
            else:
                formula = lines[temp[line.assumptions[1]]].formula
                temp_formula_1 = Formula('->', formula.first,  formula.second.first)
                temp_formula_2 = Formula('->', formula.first, formula.second.second)
                temp_formula_3 = Formula('->', temp_formula_1, temp_formula_2)
                lines.append(Proof.Line(Formula('->', formula, temp_formula_3), D, []))
                lines.append(Proof.Line(temp_formula_3, MP, [temp[line.assumptions[1]], len(lines)-1]))
                formula_new = Formula('->', antecedent, line.formula)
                lines.append(Proof.Line(formula_new, MP, [temp[line.assumptions[0]], len(lines)-1]))

        temp[i] = len(lines)-1
        i += 1

    rules = []
    for rule in proof.rules:
        rules.append(rule)
    rules.append(MP)
    rules.append(I0)
    rules.append(I1)
    rules.append(D)
    rules = set(rules)

    return Proof(statement, rules, lines)


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)


def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    temp_proof = remove_assumption(proof)

    rules = {MP, I0, I1, D, N, NI}
    assumptions = temp_proof.statement.assumptions

    phi = proof.statement.assumptions[len(proof.statement.assumptions)-1].first
    str_phi = str(phi)
    shift_size = len(temp_proof.lines)
    new_lines = []
    for line in temp_proof.lines:
        new_lines.append(line)

    temp_formula_1 = Formula.parse('((~' + str_phi + '->~(p->p))->((p->p)->' + str_phi + '))')
    temp_formula_2 = Formula.parse('((p->p)->' + str_phi + ')')
    temp_formula_3 = Formula.parse('(p->p)')

    new_line_1 = Proof.Line(temp_formula_1, N, [])
    new_lines.append(new_line_1)
    new_line_2 = Proof.Line(temp_formula_2, MP, [shift_size-1, shift_size])
    new_lines.append(new_line_2)
    new_line_3 = Proof.Line(temp_formula_3, I0, [])
    new_lines.append(new_line_3)
    last_line = Proof.Line(phi, MP, [shift_size+2, shift_size+1])
    new_lines.append(last_line)

    new_statement = InferenceRule(assumptions, phi)
    return Proof(new_statement, rules, new_lines)


