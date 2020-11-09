# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.operators import *
from propositions.axiomatic_systems import *


def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    constructed_formulas_str = []
    for var in model:
        constructed_formulas_str.append(var)
    constructed_formulas_str = sorted(constructed_formulas_str)

    constructed_formulas = []
    for var in constructed_formulas_str:
        if model[var]:
            constructed_formulas.append(Formula(var))
        else:
            constructed_formulas.append((Formula('~', Formula(var))))
    return constructed_formulas


def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    rules = AXIOMATIC_SYSTEM
    assumptions = formulae_capturing_model(model)

    conclusion = formula
    value_of_formula = evaluate(formula, model)

    if not value_of_formula:
        conclusion = Formula('~', formula)

    statement = InferenceRule(assumptions, conclusion)

    if is_variable(str(formula)) or (is_unary(str(conclusion.root)) and is_variable(str(conclusion.first))):
        lines = [Proof.Line(conclusion)]
        return Proof(statement, rules, lines)

    elif is_binary(str(formula.root)):
        if value_of_formula:
            if not evaluate(formula.first, model):
                antecedent_proof = prove_in_model(Formula('~', formula.first), model)
                return prove_corollary(antecedent_proof, conclusion, I2)
            elif evaluate(formula.second, model):
                antecedent_proof = prove_in_model(formula.second, model)
                return prove_corollary(antecedent_proof, conclusion, I1)
        else:
            antecedent_proof_1 = prove_in_model(formula.first, model)
            antecedent_proof_2 = prove_in_model(Formula('~', formula.second), model)
            return combine_proofs(antecedent_proof_1, antecedent_proof_2, conclusion, NI)

    elif is_unary(str(formula.root)):
        if value_of_formula:
            return prove_in_model(formula.first, model)
        else:
            antecedent_proof = prove_in_model(formula.first, model)
            return prove_corollary(antecedent_proof, conclusion, NN)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2

    antecedent_proof_1 = remove_assumption(proof_from_affirmation)
    antecedent_proof_2 = remove_assumption(proof_from_negation)
    return combine_proofs(antecedent_proof_1, antecedent_proof_2,
                          proof_from_affirmation.statement.conclusion, R)


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    if model is not None and len(tautology.variables()) == len(model):
        return prove_in_model(tautology, model)
    else:
        variables = sorted(tautology.variables())
        new_model_1 = dict()
        if model is not None:
            for var in model.keys():
                new_model_1[var] = model[var]
        new_model_2 = deepcopy(new_model_1)
        for var in variables:
            if var not in model.keys():
                new_model_1[var] = True
                new_model_2[var] = False
                antecedent_proof_1 = prove_tautology(tautology, new_model_1)
                antecedent_proof_2 = prove_tautology(tautology, new_model_2)
                return reduce_assumption(antecedent_proof_1, antecedent_proof_2)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    if is_tautology(formula):
        return prove_tautology(formula, {})
    else:
        models = all_models(list(formula.variables()))
        for model in models:
            if not evaluate(formula, model):
                return model


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    if rule.assumptions is None:
        return rule.conclusion
    else:
        inner = Formula('->', rule.assumptions[-1], rule.conclusion)
        outer = deepcopy(inner)
        i = len(rule.assumptions)-2
        while i >= 0:
            outer = Formula('->', rule.assumptions[i], inner)
            inner = deepcopy(outer)
            i -= 1
        return outer


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    if len(rule.assumptions) == 0 :
        return prove_tautology(rule.conclusion)
    else:
        formula = encode_as_formula(rule)
        tautology_proof = prove_tautology(formula)
        rules = AXIOMATIC_SYSTEM
        statement = rule
        lines = [Proof.Line(assumption) for assumption in rule.assumptions]
        shift_size = len(lines)

        for line in tautology_proof.lines:
            l_formula = line.formula
            l_rule = line.rule
            l_assumptions = []
            for assump in line.assumptions:
                l_assumptions.append(assump + shift_size)
            lines.append(Proof.Line(l_formula, l_rule, l_assumptions))

        for i in range(len(rule.assumptions)):
            lines.append(Proof.Line(formula.second, MP, [i, len(lines) - 1]))
            formula = formula.second

        return Proof(statement, rules, lines)


def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    variables = []
    for formula in formulae:
        variables += formula.variables()

    formulas_satisfiable_by_model = 0
    for model in all_models(variables):
        formulas_satisfiable_by_model = 0
        for formula in formulae:
            if not evaluate(formula, model):
                formulas_satisfiable_by_model = 0
                break
            else:
                formulas_satisfiable_by_model += 1
                if formulas_satisfiable_by_model == len(formulae):
                    return model

    rule = InferenceRule(list(formulae),Formula.parse('~(p->p)'))
    return prove_sound_inference(rule)



def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
