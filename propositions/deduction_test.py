# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction_test.py

"""Tests for the propositions.deduction module."""

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.deduction import *

from propositions.proofs_test import offending_line

def test_prove_corollary(debug=False):
    x = Formula('x')
    y = Formula('y')
    
    pf = Proof(InferenceRule([x],x), AXIOMATIC_SYSTEM, [Proof.Line(x)])
    g1 = Formula.parse('~~x')
    r1 = NN

    g2 = Formula.parse('(y->~~x)')
    r2 = I1

    g3 = Formula.parse('((~y->~~x)->~~x)')
    r3 = R
    
    for g, r in [ (g1,r1), (g2, r2), (g3,r3) ]:
        if debug:
            print('Testing prove_corollary of', g, 'from proof of',
                  pf.statement, 'using rule', r)
        pp = prove_corollary(pf, g, r)
        assert pp.rules == pf.rules
        assert pp.statement.assumptions == pf.statement.assumptions
        assert pp.statement.conclusion == g
        assert pp.is_valid(), offending_line(pp)
        pf = pp

def test_combine_proofs(debug=False):
    # test1
    p = Formula('p')
    lp = Proof.Line(p)
    q = Formula('q')
    nq = Formula('~',q)
    lnq = Proof.Line(nq)
    pfp = Proof(InferenceRule([p,nq],p), AXIOMATIC_SYSTEM, [lp])
    pfnq = Proof(InferenceRule([p,nq],nq), AXIOMATIC_SYSTEM, [lnq])
    h1 = Formula.parse('~(p->q)')

    #test2
    np = Formula('~',p)
    lnp = Proof.Line(np)
    lq = Proof.Line(q)
    nnq = Formula('~',nq)
    rip = Formula('->',Formula('r'),p)
    linesp = [lp,
              Proof.Line(Formula('->',p,rip),I1,[]),
              Proof.Line(rip, MP, [0,1])]
    linesq = [lq,
              Proof.Line(Formula('->',q,nnq),NN,[]),
              Proof.Line(nnq, MP, [0,1])]                            
    pfp2 = Proof(InferenceRule([p,q],rip), {MP,NN,I1, NI}, linesp)
    pfnq2 = Proof(InferenceRule([p,q],nnq), {MP,NN,I1, NI}, linesq)
    h2 = Formula.parse('~((r->p)->~q)')
    
    # Variant for test1.5
    pfp15 = Proof(InferenceRule([p,nq],rip), AXIOMATIC_SYSTEM, linesp)
    h15 = Formula.parse('~((r->p)->q)')

    # test3
    pp3 = Formula.parse('(x->y)')
    pq3 = Formula.parse('(~x->y)')
    y = Formula('y')
    pfp3 = Proof(InferenceRule([y],pp3), {MP, R, I0, I1},
                 [Proof.Line(y),
                  Proof.Line(Formula.parse('(y->(x->y))'),I1,[]),
                  Proof.Line(Formula.parse('(x->y)'),MP,[0,1])])
    pfq3 = Proof(InferenceRule([y],pq3), {MP, R, I0, I1},
                 [Proof.Line(y),
                  Proof.Line(Formula.parse('(y->(~x->y))'),I1,[]),
                  Proof.Line(Formula.parse('(~x->y)'),MP,[0,1])])
    h3 = y
 
    for pp, pnq, h, r in [(pfp,pfnq,h1,NI),(pfp15,pfnq, h15, NI),
                          (pfp2,pfnq2, h2, NI), (pfp3,pfq3,h3,R)]:
        if debug:
            print('Testing combine_proof of', h,'from', pp.statement, 'and',
                  pnq.statement, 'using rule', r)
        pnpiq = combine_proofs(pp, pnq, h, r)
        assert pnpiq.rules == pp.rules
        assert pnpiq.statement.conclusion == h
        assert pnpiq.statement.assumptions == pp.statement.assumptions
        assert pnpiq.is_valid(), offending_line(pnpiq)


R1 = InferenceRule([Formula.parse('(p|q)'), Formula.parse('(~p|r)')],
                   Formula.parse('(q|r)'))
R2 = InferenceRule([], Formula.parse('(~p|p)'))

DISJUNCTION_COMMUTATIVITY_PROOF = Proof(
    InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)')),
    {R1, R2},
    [Proof.Line(Formula.parse('(x|y)')),
     Proof.Line(Formula.parse('(~x|x)'), R2, []),
     Proof.Line(Formula.parse('(y|x)'), R1, [0, 1])])

R3 = InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)'))
R4 = InferenceRule([Formula.parse('(x|(y|z))')],
                   Formula.parse('((x|y)|z)'))

DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF = Proof(
    InferenceRule([Formula.parse('((x|y)|z)')],
                  Formula.parse('(x|(y|z))')),
    {R3, R4},
    [Proof.Line(Formula.parse('((x|y)|z)')),
     Proof.Line(Formula.parse('(z|(x|y))'), R3, [0]),
     Proof.Line(Formula.parse('((z|x)|y)'), R4, [1]),
     Proof.Line(Formula.parse('(y|(z|x))'), R3, [2]),
     Proof.Line(Formula.parse('((y|z)|x)'), R4, [3]),
     Proof.Line(Formula.parse('(x|(y|z))'), R3, [4])])

R5 = InferenceRule([], Formula.parse('(((x|y)|z)->(x|(y|z)))'))
R6 = InferenceRule([], Formula.parse('((x|y)->(y|x))'))
R7 = InferenceRule([], Formula.parse('(~p|p)'))

DISJUNCTION_ROTATION_PROOF = Proof(
    InferenceRule([Formula.parse('((p|q)|r)')],
                  Formula.parse('((r|p)|q)')),
    {MP, I1, I2, R5, R6, R7},
    [Proof.Line(Formula.parse('(((p|q)|r)->(p|(q|r)))'), R5, []),
     Proof.Line(Formula.parse('((p|(q|r))->((q|r)|p))'), R6, []),
     Proof.Line(Formula.parse('(((q|r)|p)->(q|(r|p)))'), R5, []),
     Proof.Line(Formula.parse('((q|(r|p))->((r|p)|q))'), R6, []),
     Proof.Line(Formula.parse('((p|q)|r)')),
     Proof.Line(Formula.parse('(p|(q|r))'), MP, [4, 0]),
     Proof.Line(Formula.parse('((q|r)|p)'), MP, [5, 1]),
     Proof.Line(Formula.parse('(q|(r|p))'), MP, [6, 2]),
     Proof.Line(Formula.parse('((r|p)|q)'), MP, [7, 3])])

# Used in remove_assumption
def prove_from_encoding(rule):
    """Given a rule [a1, a2, ..., ak] => c, return a proof for it that uses as
    its rules MP as well as a single new rule that has no assumptions and whose
    conclusion is (a1->(a2->...(ak->c)...))"""
    assert type(rule) is InferenceRule
    f = rule.conclusion
    for a in reversed(rule.assumptions):
        f = Formula('->', a, f)
    newrule = InferenceRule([], f)
    lines = []
    for a in rule.assumptions:
        lines.append(Proof.Line(a))
    lines.append(Proof.Line(f, newrule, []))
    for i in range(len(rule.assumptions)):
        lines.append(Proof.Line(lines[-1].formula.second, MP, [i,len(lines)-1]))
    return Proof(rule, {MP, newrule}, lines)

def test_prove_from_encoding(debug=True):
    from propositions.some_proofs import prove_and_commutativity
    from propositions.tautology import encode_as_formula

    for p in [DISJUNCTION_COMMUTATIVITY_PROOF,
              prove_and_commutativity(),
              DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF]:
        for r in p.rules:
            if(debug):
                print("\nTesting prove_from_encoding on:", r)
            pp = prove_from_encoding(r)
            if(debug):
                print("Got:", pp)
            assert pp.statement == r
            newrule = InferenceRule([], encode_as_formula(r))
            assert pp.rules == {newrule,MP}
            assert pp.is_valid(), offending_line(pp)
            
def test_remove_assumption(debug=False):
    from propositions.some_proofs import prove_and_commutativity

    for oldp in [DISJUNCTION_COMMUTATIVITY_PROOF,
                 prove_and_commutativity(),
                 DISJUNCTION_RIGHT_ASSOCIATIVITY_PROOF,
                 DISJUNCTION_ROTATION_PROOF]:
        p = oldp
        assert p.is_valid(), offending_line(p)
        while(True):
            rb = None
            for r in p.rules:
                if r != MP and len(r.assumptions) > 0:
                    rb = r
                    break
            if rb is None:
                break
            pr = prove_from_encoding(rb)
            p = inline_proof(p, pr)
        assert p.is_valid(), offending_line(p)
        if debug:
            print("Testing remove_assumption on:", p)
        pp = remove_assumption(p)
        if debug:
            print("Got:", pp)
        assert pp.statement.assumptions == p.statement.assumptions[:-1]
        assert pp.statement.conclusion == Formula('->',
                                                  p.statement.assumptions[-1],
                                                  p.statement.conclusion)
        assert pp.rules.issubset(p.rules.union({MP,I0,I1,D}))
        assert pp.is_valid(), offending_line(pp)

def test_proof_from_inconsistency(debug=False):
    assumptions = (Formula.parse('(~~p->~~q)'), Formula.parse('p'),
                   Formula.parse('~q'))
    rules = {MP, I1, N, NI}
    pf = Proof(InferenceRule(assumptions, Formula.parse('(q->p)')), rules,
               [Proof.Line(Formula.parse('p')),
                Proof.Line(Formula.parse('(p->(q->p))'), I1, []),
                Proof.Line(Formula.parse('(q->p)'), MP, [0, 1])
               ])
    pnf = Proof(InferenceRule(assumptions, Formula.parse('~(q->p)')), rules,
                [Proof.Line(Formula.parse('(~~p->~~q)')),
                 Proof.Line(Formula.parse('((~~p->~~q)->(~q->~p))'), N, []),
                 Proof.Line(Formula.parse('(~q->~p)'), MP, [0, 1]),
                 Proof.Line(Formula.parse('((~q->~p)->(p->q))'), N, []),
                 Proof.Line(Formula.parse('(p->q)'), MP, [2, 3]),
                 Proof.Line(Formula.parse('p')),
                 Proof.Line(Formula.parse('q'), MP, [5, 4]),
                 Proof.Line(Formula.parse('~q')),
                 Proof.Line(Formula.parse('~p'), MP, [7, 2]),
                 Proof.Line(Formula.parse('(q->(~p->~(q->p)))'), NI, []),
                 Proof.Line(Formula.parse('(~p->~(q->p))'), MP, [6, 9]),
                 Proof.Line(Formula.parse('~(q->p)'), MP, [8, 10])
                ])
    g = Formula.parse('(p->r)')
    if debug:
        print("Testing proof_from_inconsistency with assumptions", assumptions,
              "and conclusion", g)
    p = proof_from_inconsistency(pf, pnf, g)
    assert p.statement.conclusion == g
    assert p.statement.assumptions == assumptions
    assert p.rules == rules.union({I2})
    assert p.is_valid(), offending_line(p)

def test_prove_by_contradiction(debug=False):
    assumptions = (Formula.parse('(~r->p)'), Formula.parse('~p'),
                   Formula.parse('~r'))
    p = Proof(InferenceRule(assumptions, Formula.parse('~(p->p)')), {MP, NI},
              [Proof.Line(Formula.parse('~r')),
               Proof.Line(Formula.parse('(~r->p)')),
               Proof.Line(Formula.parse('p'), MP, [0, 1]),
               Proof.Line(Formula.parse('(p->(~p->~(p->p)))'), NI, []),
               Proof.Line(Formula.parse('(~p->~(p->p))'), MP, [2, 3]),
               Proof.Line(Formula.parse('~p')),
               Proof.Line(Formula.parse('~(p->p)'), MP, [5, 4])
              ])
    if debug:
        print("Testing prove_by_contradiction on proof of", p.statement)
    p = prove_by_contradiction(p)
    assert p.statement.conclusion == Formula.parse('r')
    assert p.statement.assumptions == assumptions[:-1]
    assert p.rules == {MP, I0, I1, D, N, NI}
    assert p.is_valid(), offending_line(p)

def test_ex5(debug=False):
    test_prove_corollary(debug)
    test_combine_proofs(debug)
    test_remove_assumption(debug)
    test_proof_from_inconsistency(debug)
    test_prove_by_contradiction(debug)

def test_all(debug=False):
    test_prove_from_encoding(debug)
    test_ex5(debug)
