# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    dict = {'-&': Formula.parse('~(p&q)'),
            '-|': Formula.parse('~(p|q)'),
            'F': Formula.parse('(p&~p)'),
            'T': Formula.parse('(p|~p)'),
            '->': Formula.parse('(~p|(p&q))'),
            '<->': Formula.parse('((p&q)|(~p&~q))'),
            '+': Formula.parse('((p&~q)|(~p&q))')}
    return Formula.substitute_operators(formula, dict)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    dict = {'T': Formula.parse('~(p&~p)'),
            'F': Formula.parse('~~(p&~p)'),
            '|': Formula.parse('~(~p&~q)'),
            '-&': Formula.parse('~(p&q)'),
            '-|': Formula.parse('~~(~p&~q)'),
            '->': Formula.parse('~(~(p&q)&p)'),
            '<->': Formula.parse('~~(~(p&~q)&~(~p&q))'),
            '+': Formula.parse('~(~(p&~q)&~(~p&q))')}
    return Formula.substitute_operators(formula, dict)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    dict = binary_nand={'T': Formula.parse_prefix('(p-&(p-&p))')[0],
                        'F': Formula.parse_prefix('((p-&(p-&p))-&(p-&(p-&p)))')[0],
                        '|': Formula.parse_prefix('((p-&p)-&(q-&q))')[0],
                        '~': Formula.parse_prefix('(p-&p)')[0],
                        '+': Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0],
                        '<->': Formula('-&',Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0]
                        , Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0]),
                        '&': Formula.parse_prefix('((p-&q)-&(p-&q))')[0],
                        '-|': Formula.parse_prefix('(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))')[0],
                        '->': Formula.parse_prefix('((p-&q)-&((p-&q)-&(p-&p)))')[0],
                        }
    return Formula.substitute_operators(formula, dict)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    temp = to_not_and(formula)
    dict = {'&':Formula.parse_prefix('~(p->~(p->q))')[0]}
    return temp.substitute_operators(dict)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    dict = {'~':Formula.parse_prefix('(p->F)')[0]}
    return to_implies_not(formula).substitute_operators(dict)
