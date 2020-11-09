# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    f, replacer = model.function_meanings, function_name_to_relation_name
    new_meaning = dict(model.relation_meanings)
    for name in model.function_meanings:
        new_meaning[replacer(name)] = {(f[name][k],) + k for k in f[name].keys()}
    return Model(model.universe.copy(), model.constant_meanings, new_meaning, dict())


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    new_functions, new_relations = dict(model.function_meanings), dict()
    for name in model.relation_meanings:
        if relation_name_to_function_name(name) in original_functions:
            func_dict = {}
            # creating the dict that defines the func from tuples of relation
            relation_tuples = list(model.relation_meanings[name])
            for t in relation_tuples:
                if t[1:] in func_dict:
                    # which means that the function has more than 1 meaning = no model exists
                    return
                func_dict[t[1:]] = t[0]
            if len(func_dict) != len(model.universe) ** (len(relation_tuples[0]) - 1):
                # function doesn't have solution for each combo
                return
            # adding the new function
            new_functions[relation_name_to_function_name(name)] = func_dict
        else:
            # not a relation we want to convert - stays a relation
            new_relations[name] = model.relation_meanings[name]
    return Model(model.universe.copy(), model.constant_meanings, new_relations, new_functions)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3

    args, steps = helper(term.arguments)
    steps.append(Formula("=", [Term(next(fresh_variable_name_generator)), Term(term.root, args)]))
    return steps


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    replace = replace_functions_with_relations_in_formula
    if is_unary(formula.root):
        return Formula("~", replace(formula.first))
    elif is_binary(formula.root):
        first = replace(formula.first)
        second = replace(formula.second)
        return Formula(formula.root, first, second)
    elif is_quantifier(formula.root):
        predicate = replace(formula.predicate)
        return Formula(formula.root, formula.variable, predicate)
    # relations or equality
    args, steps = helper(formula.arguments)
    formula = Formula(formula.root, args)
    for step in steps[::-1]:
        x, y = step.arguments  # step : x= y
        first = function_name_to_relation_name(y.root)
        second = [Term(x.root)] + list(y.arguments)
        formula = Formula('A', x.root, Formula('->', Formula(first, second), formula))
    return formula


def helper(arguments):
    """
    this helper goes through arguments and compile them if needed
    :param arguments: arguments to go through
    :return: list of arguments (compiled), and list of steps it took
    """
    args, steps = [], []
    for term in arguments:
        if is_function(term.root):
            steps += compile_term(term)
            term = steps[-1].arguments[0]
        args.append(Term(term.root))
    return args, steps


def replace_functions_with_relations_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5

    formulas_to_return = set()
    for formula in formulas:

        formulas_to_return.update({replace_functions_with_relations_in_formula(formula)})

        for func in formula.functions():
            num_of_args = func[1]
            str_temp1 = ""
            str_temp2 = ""
            for arg in range(num_of_args):
                str_temp1 += "Ax" + str(arg+1) + "["
                str_temp2 += "Ax" + str(arg+1) + "["
            str_temp1 += "Ez[" + function_name_to_relation_name(func[0]) + "(z,"
            str_temp2 += "Az1[Az2[((" + function_name_to_relation_name(func[0]) + "(z1,"
            str_temp3 = "&" + function_name_to_relation_name(func[0]) + "(z2,"
            for arg in range(num_of_args-1):
                str_temp1 += "x" + str(arg+1) + ","
                str_temp2 += "x" + str(arg+1) + ","
                str_temp3 += "x" + str(arg+1) + ","
            str_temp1 += "x" + str(num_of_args) + ")"
            str_temp2 += "x" + str(num_of_args) + ")"
            str_temp3 += "x" + str(num_of_args) + ")"
            str_temp2 += str_temp3 + ")->z1=z2)"
            for i in range(num_of_args):
                str_temp1 += "]"
                str_temp2 += "]"
            str_temp2 += "]]"
            formulas_to_return.update({Formula('&', Formula.parse(str_temp1), Formula.parse(str_temp2))})
    return formulas_to_return


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6
    formulas_to_return = {
        Formula.parse("Ax[SAME(x,x)]"),
        Formula.parse("Ax[Ay[(SAME(x,y)->SAME(y,x))]]"),
        Formula.parse("Ax[Ay[Az[((SAME(x,y)&SAME(y,z))->SAME(x,z))]]]")}

    for formula in formulas:
        formulas_to_return.update({replace_equality_with_SAME_in_formula(formula)})

        for relation in formula.relations():
            num_of_args = relation[1]
            if num_of_args == 0:  # ignore when relation is nullary
                continue
            else:
                str_temp1 = ""
                str_temp3 = relation[0] + "("
                str_temp4 = relation[0] + "("
                for arg in range(num_of_args * 2):
                    str_temp1 += "Ax" + str(arg + 1) + "["
                str_temp2 = SAME_helper1(num_of_args, Formula.parse("SAME(x1,x2)"))
                for arg in range(num_of_args * 2 ):
                    if arg % 2 == 0:
                        str_temp3 += "x"+str(arg+1)+","
                    else:
                        str_temp4 += "x"+str(arg+1)+","
                str_temp3 = Formula.parse(str_temp3[:-1] + ")")
                str_temp4 = Formula.parse(str_temp4[:-1] + ")")
                temp_formula = Formula('->', str_temp2, Formula('->', str_temp3, str_temp4))
                formula_to_return = Formula.parse(str_temp1+str(temp_formula) + ("]" * num_of_args * 2))
                formulas_to_return.update({formula_to_return})
    return formulas_to_return


def SAME_helper1(num_of_args: int, formula: Optional[Formula])-> \
        Formula:
    if num_of_args == 1:
        return formula
    else:
        f = Formula('&', formula, Formula.parse('SAME(x'+str(num_of_args*2-1)+',x'+str(num_of_args*2)+')'))
        return SAME_helper1(num_of_args-1, f)

def replace_equality_with_SAME_in_formula(formula: Formula) -> Formula:
    if is_equality(formula.root):
        return Formula('SAME', formula.arguments)
    elif is_relation(formula.root):
        return formula
    elif is_unary(formula.root):
        return Formula(formula.root, replace_equality_with_SAME_in_formula(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root, replace_equality_with_SAME_in_formula(formula.first),
                       replace_equality_with_SAME_in_formula(formula.second))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable,
                       replace_equality_with_SAME_in_formula(formula.predicate))


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    relation_meaning = dict(model.relation_meanings)
    relation_meaning['SAME'] = {(x, x) for x in model.universe}
    return Model(model.universe, model.constant_meanings, relation_meaning, model.function_meanings)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
    universe = list()
    equivalence_classes = {}
    SAME_relation = model.relation_meanings['SAME']
    for val in SAME_relation:
        if val[0] not in universe:
            universe.append(val[0])
            equivalence_classes[val[0]] = [val[0]]

    for val1 in universe:
        for val2 in universe:
            if val1 != val2 and(val1, val2) in SAME_relation:
                universe.remove(val2)
                del (equivalence_classes[val2])
                equivalence_classes[val1].append(val2)

    relation_meanings = dict()

    for relation in model.relation_meanings.keys():
        if relation != 'SAME':
            relation_meanings[relation] = set()
            for meaning in model.relation_meanings[relation]:
                for v in meaning:
                    if v not in universe:
                        meaning = get_new_meaning(meaning, v, equivalence_classes)
                relation_meanings[relation].add(meaning)

    constant_meanings = dict()
    for constant in model.constant_meanings.keys():
        if model.constant_meanings[constant] in universe:
            constant_meanings[constant] = model.constant_meanings[constant]
        else:
            constant_meanings[constant] = get_constant_meaning(
                model.constant_meanings[constant], equivalence_classes)
    return Model(universe, constant_meanings, relation_meanings)


def get_constant_meaning(curr_meaning: T, equivalence_classes)-> T:
    for key in equivalence_classes.keys():
        if curr_meaning in equivalence_classes[key]:
            return key


def get_new_meaning(meaning: tuple, v: T, equivalence_classes) -> tuple:
    new_meaning = list()
    for val in meaning:
        if val != v:
            new_meaning.append(val)
    for key in equivalence_classes.keys():
        if v in equivalence_classes[key]:
            new_meaning.append(key)
            break
    return tuple(new_meaning)