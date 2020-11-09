# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/axiomatic_systems.py

"""Axiomatic inference rules of propositional logic."""

from propositions.proofs import *

# Axiomatic inference rules that only contain implies

#: Modus ponens / implication elimination
MP = InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')],
                   Formula.parse('q'))
#: Self implication
I0 = InferenceRule([], Formula.parse('(p->p)'))
#: Implication introduction (right)
I1 = InferenceRule([], Formula.parse('(q->(p->q))'))
#: Self-distribution of implication
D = InferenceRule([], Formula.parse('((p->(q->r))->((p->q)->(p->r)))'))

# Axiomatic inference rules for not (and implies)

#: Implication introduction (left)
I2 = InferenceRule([], Formula.parse('(~p->(p->q))'))
#: Converse contraposition
N  = InferenceRule([], Formula.parse('((~q->~p)->(p->q))'))
#: Negative-implication introduction
NI = InferenceRule([], Formula.parse('(p->(~q->~(p->q)))'))
#: Double-negation introduction
NN = InferenceRule([], Formula.parse('(p->~~p)'))
#: Resolution
R  = InferenceRule([], Formula.parse('((q->p)->((~q->p)->p))'))

#: Large axiomatic system for implication and negation, consisting of `MP`,
#: `I0`, `I1`, `D`, `I2`, `N`, `NI`, `NN`, `R`.
AXIOMATIC_SYSTEM = {MP, I0, I1, D, I2, N, NI, NN, R}
#: Hilbert axiomatic system for implication and negation, consisting of `MP`,
#: `I1`, `D`, `N`.
HILBERT_AXIOMATIC_SYSTEM = {MP, I1, D, N}

# Axiomatic inference rules for conjunction (and implication and negation)

#: Conjunction introduction
A   = InferenceRule([], Formula.parse('(p->(q->(p&q)))'))
#: Negative conjunction introduction (right)
NA1 = InferenceRule([], Formula.parse('(~q->~(p&q))'))
#: Negative conjunction introduction (left)
NA2 = InferenceRule([], Formula.parse('(~p->~(p&q))'))

# Axiomatic inference rules for disjunction (and implication and negation)

# Disjunction introduction (right)
O1  = InferenceRule([], Formula.parse('(q->(p|q))'))
# Disjunction introduction (left)
O2  = InferenceRule([], Formula.parse('(p->(p|q))'))
# Negative-disjunction introduction
NO  = InferenceRule([], Formula.parse('(~p->(~q->~(p|q)))'))

# Axiomatic inference rules for constants (and implication and negation)

#: Truth introduction
T   =  InferenceRule([], Formula.parse('T'))
#: Negative falsity introduction
NF  = InferenceRule([], Formula.parse('~F'))

#: Large axiomatic system for all operators, consisting of the rules in
#: `AXIOMATIC_SYSTEM`, as well as `A`, `NA1`, `NA2`, `O1`, `O2`, `NO`, `T`,
#: `NF`.
AXIOMATIC_SYSTEM_FULL = AXIOMATIC_SYSTEM.union({A, NA1, NA2, O1, O2, NO, T, NF})

# Alternative for N

#: Reductio ad absurdum
N_ALTERNATIVE = InferenceRule([], Formula.parse('((~q->~p)->((~q->p)->q))'))

#: Hilbert axiomatic system for implication and negation, with `N` replaced by
#: `N_ALTERNATIVE`.
HILBERT_AXIOMATIC_SYSTEM_ALTERNATIVE = {MP, I1, I2, N_ALTERNATIVE}

# Alternatives for NA1, NA2, NO without negation

#: Conjunction elimination (right)
AE1 = InferenceRule([], Formula.parse('((p&q)->q)'))
#: Conjunction elimination (left)
AE2 = InferenceRule([], Formula.parse('((p&q)->p)'))
#: Disjunction elimination
OE = InferenceRule([], Formula.parse('((p->r)->((q->r)->((p|q)->r)))'))

#: Hilbert axiomatic system for all operators, consisting of the rules in
#: `HILBERT_AXIOMATIC_SYSTEM`, as well as `A`, `AE1`, `AE2`, `O1`, `O2`, `OE`,
#: `T`, `NF`.
HILBERT_AXIOMATIC_SYSTEM_FULL = \
    HILBERT_AXIOMATIC_SYSTEM.union({A, AE1, AE2, O1, O2, OE, T, NF})
