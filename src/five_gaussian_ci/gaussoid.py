"""Gaussoid axioms and the complete four-variable Gaussian catalogue filter."""
from __future__ import annotations
from itertools import permutations
from .atoms import Atom, atoms

def is_gaussoid(S, universe):
    U=tuple(sorted(universe)); S=frozenset(S)
    for i,j,k in permutations(U,3):
        rest=[x for x in U if x not in (i,j,k)]
        for mask in range(1<<len(rest)):
            L=frozenset(rest[b] for b in range(len(rest)) if mask&(1<<b))
            ij=Atom(min(i,j),max(i,j),L); ikj=Atom(min(i,k),max(i,k),L|{j})
            ik=Atom(min(i,k),max(i,k),L); ijk=Atom(min(i,j),max(i,j),L|{k})
            if ij in S and ikj in S and not (ik in S and ijk in S): return False
            if ijk in S and ikj in S and not (ij in S and ik in S): return False
            if ij in S and ik in S and not (ijk in S and ikj in S): return False
            if ij in S and ijk in S:
                jk=Atom(min(j,k),max(j,k),L)
                if ik not in S and jk not in S:return False
    return True

def lm_higher_rules_4():
    """All ordered instances of Lnenicka--Matus (2007), Lemma 10, (17)--(21), L=empty."""
    out=[]
    for i,j,k,l in permutations((1,2,3,4)):
        A=lambda x,y,K=(): Atom(min(x,y),max(x,y),frozenset(K))
        out += [
          ((A(i,j),A(k,l),A(i,k,(j,l)),A(j,l,(i,k))),A(i,k)),
          ((A(i,j),A(k,l,(i,)),A(k,l,(j,)),A(i,j,(k,l))),A(k,l)),
          ((A(i,j),A(j,l,(k,)),A(k,l,(i,)),A(i,k,(j,l))),A(i,k)),
          ((A(i,j,(k,)),A(i,k,(l,)),A(i,l,(j,))),A(i,j)),
          ((A(i,j,(k,)),A(i,k,(l,)),A(j,l,(i,)),A(k,l,(j,))),A(i,j)),
        ]
    # exact deduplication while preserving order
    seen=set(); ans=[]
    for p,c in out:
        key=(frozenset(p),c)
        if key not in seen: seen.add(key); ans.append((frozenset(p),c))
    return tuple(ans)

def satisfies_lm_higher_4(S):
    S=frozenset(S)
    return all(not (p<=S) or c in S for p,c in lm_higher_rules_4())

def decode_zero_means_member(bits, universe):
    A=atoms(universe); bits=bits.strip()
    if len(bits)!=len(A) or set(bits)-{'0','1'}: raise ValueError("bad bitstring")
    return frozenset(a for a,b in zip(A,bits) if b=='0')
