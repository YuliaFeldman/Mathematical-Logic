# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping
from itertools import product
from propositions.syntax import *
from propositions.proofs import *


Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1

    def evaluate_constant(formula: Formula) -> bool:
        if formula.root == 'T':
            return True
        return False

    def evaluate_variable(formula: Formula) -> bool:
        return model[formula.root]

    def evaluate_unary(formula: Formula) -> bool:
        return not evaluate(formula.first, model)

    def evaluate_binary(formula: Formula) -> bool:
        if formula.root == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == '->':
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            if first and not second:
                return False
            return True
        elif formula.root == '+':
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            if (first and not second) or (not first and second):
                return True
            return False
        elif formula.root == '<->':
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            if (first and second) or (not first and not second):
                return True
            return False
        elif formula.root == '-&':
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            if first and second:
                return False
            return True
        elif formula.root == '-|':
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            if (not first) and (not second):
                return True
            return False

    if is_constant(formula.root):
        return evaluate_constant(formula)
    elif is_variable(formula.root):
        return evaluate_variable(formula)
    elif is_unary(formula.root):
        return evaluate_unary(formula)
    elif is_binary(formula.root):
        return evaluate_binary(formula)


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        # >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2

    product_result = product([False, True], repeat=len(variables))
    models = []
    for model in product_result:
        temp_model = iter(model)
        result_temp = {}
        for v in variables:
            result_temp[v] = next(temp_model)
        models.append(result_temp)
    return models


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    truth_vals = []
    for model in models:
        truth_vals.append(evaluate(formula, model))
    return truth_vals


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        #>>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    temp_vars = formula.variables()
    vars = sorted(temp_vars)
    models = list(all_models(vars))

    # get the width of each column in the table
    width_of_cols = []
    for var in vars:
        width_of_cols.append(len(var) + 2)
    width_of_cols.append(len(str(formula))+2)

    # translate boolean values to strings
    models_temp1 = []
    models_temp2 = []
    for m in models:
        models_temp1 += m.values()
    for val in models_temp1:
        if val:
            models_temp2 += 'T'
        else:
            models_temp2 += 'F'

    num_of_rows = len(models)
    num_of_cols = len(vars) + 1

    # print header line
    header_line = "|"
    for var in vars:
        header_line += " " + var + " |"
    header_line += " " + str(formula) + " |"
    print(header_line)

    # print separation line
    separate_line = "|"
    for width in width_of_cols:
        separate_line += '-'*width + '|'
    print(separate_line)

    # print values of truth table
    for i in range(num_of_rows):
        line = "| "
        for j in range(num_of_cols):
            if j != num_of_cols - 1:
                line += models_temp2[0]
                models_temp2.pop(0)
                line += " " * (width_of_cols[j] - 2) + "| "
            else:
                if evaluate(formula, models[i]):
                    line += 'T'
                else:
                    line += 'F'
                line += " " * (width_of_cols[j] - 2) + "|"
        print(line)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    variables_list = formula.variables()
    models = all_models(list(variables_list))
    truth_values_list = truth_values(formula, models)
    if False in truth_values_list:
        return False
    return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    variables_list = formula.variables()
    models = all_models(list(variables_list))
    truth_values_list = truth_values(formula, models)
    if True in truth_values_list:
        return False
    return True


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    variables_list = formula.variables()
    models = all_models(list(variables_list))
    truth_values_list = truth_values(formula, models)
    if True in truth_values_list:
        return True
    return False


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6
    variables_list = list(variables(model))

    # if there is only one variable in the given model
    if len(variables_list) == 1:
        if model[variables_list[0]]:
            return Formula(variables_list[0])
        return Formula('~', Formula(variables_list[0]))

    # otherwise
    if model[variables_list[0]]:
        f1 = Formula(variables_list[0])
    else:
        f1 = Formula('~', Formula(variables_list[0]))
    if model[variables_list[1]]:
        f2 = Formula(variables_list[1])
    else:
        f2 = Formula('~', Formula(variables_list[1]))
    formula = temp_formula = Formula('&', f1, f2)

    # if there ara more than two variables in the given model
    for i in range(2, len(variables_list)):
        if model[variables_list[i]]:
            formula = Formula('&', temp_formula, Formula(variables_list[i]))
        else:
            formula = Formula('&', temp_formula, Formula('~', Formula(variables_list[i])))
        temp_formula = formula

    return formula


def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        #>>> formula = synthesize(['p', 'q'], [True, True, True, False])
        #>>> for model in all_models(['p', 'q']):
        #...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    values = list(values)
    models = list(all_models(variables))

    synthesized_formulas = []
    for model in models:
        synthesized_formulas.append(synthesize_for_model(model))

    formula = temp_formula = None
    j = 0
    for i in range(len(values)):
        if values[i]:
            formula = temp_formula = synthesized_formulas[i]
            j = i
            break

    if formula is not None:
        for i in range(j+1,len(values)):
            if values[i]:
                formula = Formula('|', temp_formula, synthesized_formulas[i])
                temp_formula = formula

    else:
        temp = []
        for var in variables:
            temp.append(Formula('&', Formula(var), Formula('~', Formula(var))))
        formula = temp_formula = temp[0]
        for i in range(1, len(temp)):
            formula = Formula('|', temp_formula, temp[i])
            temp_formula = formula

    return formula

# Tasks for Chapter 4


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2

    truth_values_of_assumptions = []
    for assumption in rule.assumptions:
        truth_values_of_assumptions.append(evaluate(assumption, model))
    if False not in truth_values_of_assumptions and not evaluate(rule.conclusion, model):
        return False
    return True


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    models = all_models(list(rule.variables()))
    for model in models:
        if not evaluate_inference(rule, model):
            return False
    return True
