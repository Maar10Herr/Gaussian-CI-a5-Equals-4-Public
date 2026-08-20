"""Canonical elementary-CI atoms and exact symmetry/minor operations."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations, permutations
from typing import Iterable, Iterator, Mapping

@dataclass(frozen=True, order=True)
class Atom:
    i: int
    j: int
    K: frozenset[int] = frozenset()

    def __post_init__(self) -> None:
        if self.i >= self.j:
            raise ValueError("require i < j")
        if self.i in self.K or self.j in self.K:
            raise ValueError("conditioning set must exclude endpoints")

    @property
    def support(self) -> frozenset[int]:
        return self.K | {self.i, self.j}

    def text(self) -> str:
        return f"[{self.i}{self.j}|{''.join(map(str, sorted(self.K)))}]"

    def permute(self, mapping: Mapping[int, int]) -> "Atom":
        a, b = mapping[self.i], mapping[self.j]
        return Atom(min(a,b), max(a,b), frozenset(mapping[k] for k in self.K))

    def dual(self, universe: Iterable[int]) -> "Atom":
        U = frozenset(universe)
        if not self.support <= U:
            raise ValueError("atom not contained in universe")
        return Atom(self.i, self.j, U - {self.i, self.j} - self.K)


def atoms(universe: Iterable[int]) -> tuple[Atom, ...]:
    U = tuple(sorted(universe))
    out=[]
    for i,j in combinations(U,2):
        rem=tuple(x for x in U if x not in (i,j))
        for mask in range(1 << len(rem)):
            out.append(Atom(i,j,frozenset(rem[b] for b in range(len(rem)) if mask & (1<<b))))
    return tuple(out)


def atom_index(universe: Iterable[int]) -> dict[Atom,int]:
    return {a:i for i,a in enumerate(atoms(universe))}


def parse_atom(text: str) -> Atom:
    s=text.strip().strip('[]')
    pair, cond=s.split('|')
    if len(pair) != 2 or not pair.isdigit() or (cond and not cond.isdigit()):
        raise ValueError(text)
    i, j = sorted(map(int, pair))
    return Atom(i, j, frozenset(map(int, cond)))

Structure=frozenset[Atom]


def permute_structure(S: Structure, mapping: Mapping[int,int]) -> Structure:
    return frozenset(a.permute(mapping) for a in S)


def dual_structure(S: Structure, universe: Iterable[int]) -> Structure:
    U=tuple(universe)
    return frozenset(a.dual(U) for a in S)


def minor_structure(S: Structure, universe: Iterable[int], marginalized=(), conditioned=()) -> Structure:
    U=frozenset(universe); M=frozenset(marginalized); C=frozenset(conditioned)
    if M & C or not (M|C) <= U:
        raise ValueError("invalid minor sets")
    R=U-M-C
    return frozenset(a for a in atoms(R) if Atom(a.i,a.j,a.K|C) in S)


def canonical_structure(S: Structure, universe: Iterable[int], include_duality: bool=True) -> tuple[int,...]:
    U=tuple(sorted(universe)); idx=atom_index(U); best=None
    for p in permutations(U):
        mp=dict(zip(U,p))
        P=permute_structure(S,mp)
        for T in ((P, dual_structure(P,U)) if include_duality else (P,)):
            key=tuple(sorted(idx[a] for a in T))
            if best is None or key < best: best=key
    return best or ()


def orbit_and_stabilizer(S: Structure, universe: Iterable[int], include_duality: bool=True) -> tuple[int,int]:
    U=tuple(sorted(universe)); idx=atom_index(U); images=[]; stab=0
    original=tuple(sorted(idx[a] for a in S))
    for p in permutations(U):
        P=permute_structure(S,dict(zip(U,p)))
        for T in ((P,dual_structure(P,U)) if include_duality else (P,)):
            key=tuple(sorted(idx[a] for a in T)); images.append(key)
            if key==original: stab += 1
    return len(set(images)),stab


def rule_support(premises: Iterable[Atom], conclusion: Atom) -> frozenset[int]:
    return frozenset().union(*(a.support for a in tuple(premises)+(conclusion,)))
