# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs.py

"""Proofs by deduction in propositional logic."""

from __future__ import annotations
from typing import AbstractSet, Iterable, FrozenSet, List, Mapping, Optional, \
                   Set, Tuple, Union

from logic_utils import frozen

from propositions.syntax import *

SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in propositional logic, comprised by zero
    or more assumed propositional formulae, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Iterable[Formula], conclusion: Formula) -> \
        None:
        """Initialized an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (isinstance(other, InferenceRule) and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))
        
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        vars = set()
        for formula in self.assumptions:
            vars.update(formula.variables())
        vars.update(self.conclusion.variables())
        return vars

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """        
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        new_assumptions = []
        for formula in self.assumptions:
            new_assumptions.append(formula.substitute_variables(specialization_map))
        new_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(new_assumptions, new_conclusion)

    @staticmethod
    def merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps.

        Parameters:
            specialization_map1: first map to merge, or ``None``.
            specialization_map2: second map to merge, or ``None``.

        Returns:
            A single map containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a

        if specialization_map1 is None or specialization_map2 is None:
            return None
        for key in specialization_map1:
            if key in specialization_map2 and specialization_map1[key] != specialization_map2[key]:
                return None
        return dict(specialization_map1, **specialization_map2)
        
    @staticmethod
    def formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b
        if is_variable(general.root):
            return {general.root: specialization}

        if is_constant(general.root):
            if general.root == specialization.root:
                return {}
            else:
                return None

        if is_unary(general.root):
            if not is_unary(specialization.root):
                return None
            return InferenceRule.formula_specialization_map(general.first, specialization.first)

        if is_binary(general.root):
            if general.root != specialization.root:
                return None
            map_of_first = InferenceRule.formula_specialization_map(general.first, specialization.first)
            map_of_second = InferenceRule.formula_specialization_map(general.second, specialization.second)
            return InferenceRule.merge_specialization_maps(map_of_first, map_of_second)

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        if len(self.assumptions) != len(specialization.assumptions):
            return None

        specialization_map = InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion)

        if len(self.assumptions) != 0:
            for i in range(0, len(self.assumptions)):
                temp = InferenceRule.formula_specialization_map(self.assumptions[i], specialization.assumptions[i])
                if temp is None:
                    return None
                specialization_map = InferenceRule.merge_specialization_maps(specialization_map, temp)

        return specialization_map

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """A frozen deductive proof, comprised of a statement in the form of an
    inference rule, a set of inference rules that may be used in the proof, and
    a proof in the form of a list of lines that prove the statement via these
    inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Iterable[Proof.Line]) -> None:
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula which
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule out
                of those allowed in the proof, a specialization of which
                concludes the formula, or ``None`` if the formula is justified
                as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): a tuple of zero
                or more indices of previous lines in the proof whose formulae
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Iterable[int]] = None) -> None:
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and indices of justifying previous lines.

            Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current proof line.

            Returns:
                A string representation of the current proof line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                return str(self.formula) + ' Inference Rule ' + \
                       str(self.rule) + \
                       ((" on " + str(self.assumptions))
                        if len(self.assumptions) > 0 else '')

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None
        
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof for ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulae justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: index of the line according to which to construct the
                inference rule.

        Returns:
            The constructed inference rule, with assumptions ordered in the
            order of their indices in the specified line, or ``None`` if the
            specified line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a

        if self.lines[line_number].is_assumption():
            return None

        assumptions_list = []
        for i in self.lines[line_number].assumptions:
            assumptions_list.append(self.lines[i].formula)

        assumptions_list = tuple(assumptions_list)
        inference_rule = InferenceRule(assumptions_list, self.lines[line_number].formula)
        return inference_rule

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: index of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            then ``True`` if and only if all of the following hold:

            1. The rule specified for that line is one of the allowed inference
               rules in the current proof.
            2. Some specialization of the rule specified for that line has
               the formula justified by that line as its conclusion, and the
               formulae justified by the lines specified as the assumptions of
               that line (in the order of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        if self.lines[line_number].is_assumption():
            if self.lines[line_number].formula not in self.statement.assumptions:
                #print('A')
                return False
            return True

        if self.lines[line_number].rule not in self.rules:
            #print('B')
            return False

        for i in self.lines[line_number].assumptions:
            if i >= line_number:
                #print('C')
                return False

        line_as_inference_rule = self.rule_for_line(line_number)
        if not line_as_inference_rule.is_specialization_of(self.lines[line_number].rule):
            #print('D')
            return False

        return True

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        for i in range(0, len(self.lines)):
            if not self.is_line_valid(i):
                return False

        if self.lines[len(self.lines)-1].formula != self.statement.conclusion:
            return False

        return True

# Chapter 5 tasks


def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule into a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    sp_map = proof.statement.specialization_map(specialization)
    new_statement = specialization

    new_rules = proof.rules

    new_lines = []
    for line in proof.lines:
        new_formula = line.formula.substitute_variables(sp_map)
        if not line.is_assumption():
            new_rule = line.rule
            new_assumptions = line.assumptions
            new_lines.append(Proof.Line(new_formula, new_rule, new_assumptions))
        else:
            new_lines.append(Proof.Line(new_formula, None, None))

    return Proof(new_statement, new_rules, new_lines)


def inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line: index of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating line indices specified throughout the proof to maintain the
        validity of the proof. The set of allowed inference rules in the
        returned proof is the union of the rules allowed in the two given
        proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a
    pre_inline = list(main_proof.lines[:line_number])
    post_inline = list(main_proof.lines[line_number+1:])

    line_as_inference_rule = main_proof.rule_for_line(line_number)

    proof_of_line = prove_specialization(lemma_proof, line_as_inference_rule)

    assumptions = []
    for assumption in main_proof.statement.assumptions:
        if assumption not in assumptions:
            assumptions.append(assumption)

    assumptions_from_prev_lines = []
    for assumption in line_as_inference_rule.assumptions:
        if assumption not in main_proof.statement.assumptions:
            assumptions_from_prev_lines.append(assumption)

    for assumption in proof_of_line.statement.assumptions:
        if assumption not in assumptions_from_prev_lines and assumption not in assumptions:
            assumptions.append(assumption)
    assumptions = tuple(assumptions)

    size_of_shift = len(pre_inline)
    new_lines = pre_inline
    for line in proof_of_line.lines:
        if not line.is_assumption():
            assumptions_of_line = [assump+size_of_shift for assump in line.assumptions]
            new_line = Proof.Line(line.formula, line.rule, assumptions_of_line)
            new_lines.append(new_line)
        else:
            if line.formula in assumptions:
                new_line = Proof.Line(line.formula)
                new_lines.append(new_line)
            else:
                for assump_index in main_proof.lines[line_number].assumptions:
                    if line.formula == main_proof.lines[assump_index].formula:
                        new_lines.append(main_proof.lines[assump_index])

    size_of_shift = len(proof_of_line.lines)-1
    for line in post_inline:
        if not line.is_assumption():
            assumptions_of_line = []
            for assump_index in line.assumptions:
                if assump_index >= line_number:
                    assumptions_of_line.append(assump_index+size_of_shift)
                else:
                    assumptions_of_line.append(assump_index)
            new_line = Proof.Line(line.formula, line.rule, assumptions_of_line)
        else:
            new_line = Proof.Line(line.formula)
        new_lines.append(new_line)
    new_lines = tuple(new_lines)

    new_rules = []
    for rule in main_proof.rules:
        new_rules.append(rule)
    for rule in proof_of_line.rules:
        new_rules.append(rule)
    new_rules = set(new_rules)

    new_statement = InferenceRule(tuple(assumptions), main_proof.statement.conclusion)
    return Proof(new_statement, new_rules, new_lines)


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the rules
        allowed in the two given proofs but without the "lemma" rule proved by
        `lemma_proof`.
    """
    # Task 5.2b
    proof = main_proof
    shift_size = len(lemma_proof.lines)-1
    i = 0
    while i < (len(proof.lines)):
        if not proof.lines[i].is_assumption():
            if proof.rule_for_line(i).is_specialization_of(lemma_proof.statement):
                proof = inline_proof_once(proof, i, lemma_proof)
                i += shift_size
                continue
        i += 1

    new_rules = []
    for rule in proof.rules:
        if rule != lemma_proof.statement:
            new_rules.append(rule)
    for rule in lemma_proof.rules:
        new_rules.append(rule)
    return Proof(proof.statement, set(new_rules), proof.lines)
