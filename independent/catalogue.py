#!/usr/bin/env python3
"""Deterministically reconstruct the labelled four-variable catalogues.

This module is deliberately standard-library only.  It turns the elementary
gaussoid axioms into CNF, enumerates every satisfying assignment with a small
deterministic DPLL solver, and then applies the five Lnenicka--Matus higher
implication schemes.  No downloaded catalogue is required.
"""

from __future__ import annotations

from itertools import combinations, permutations


Atom = tuple[int, int, frozenset[int]]


def atoms(universe: tuple[int, ...]) -> tuple[Atom, ...]:
    out: list[Atom] = []
    for i, j in combinations(universe, 2):
        rest = tuple(x for x in universe if x not in (i, j))
        for mask in range(1 << len(rest)):
            conditioning = frozenset(
                rest[k] for k in range(len(rest)) if mask >> k & 1
            )
            out.append((i, j, conditioning))
    return tuple(out)


UNIVERSE = (1, 2, 3, 4)
ATOMS = atoms(UNIVERSE)
INDEX = {atom: index for index, atom in enumerate(ATOMS)}


def atom(i: int, j: int, conditioning: tuple[int, ...] = ()) -> Atom:
    return (min(i, j), max(i, j), frozenset(conditioning))


def literal(a: Atom, present: bool = True) -> int:
    """Return a DIMACS-style literal for membership of ``a``."""

    value = INDEX[a] + 1
    return value if present else -value


def gaussoid_clauses() -> tuple[tuple[int, ...], ...]:
    clauses: set[tuple[int, ...]] = set()
    for i, j, k in permutations(UNIVERSE, 3):
        rest = tuple(x for x in UNIVERSE if x not in (i, j, k))
        for mask in range(1 << len(rest)):
            background = tuple(
                rest[b] for b in range(len(rest)) if mask >> b & 1
            )
            ij = atom(i, j, background)
            ik = atom(i, k, background)
            jk = atom(j, k, background)
            ik_j = atom(i, k, background + (j,))
            ij_k = atom(i, j, background + (k,))

            raw = (
                (-literal(ij), -literal(ik_j), literal(ik)),
                (-literal(ij), -literal(ik_j), literal(ij_k)),
                (-literal(ij_k), -literal(ik_j), literal(ij)),
                (-literal(ij_k), -literal(ik_j), literal(ik)),
                (-literal(ij), -literal(ik), literal(ij_k)),
                (-literal(ij), -literal(ik), literal(ik_j)),
                (-literal(ij), -literal(ij_k), literal(ik), literal(jk)),
            )
            for clause in raw:
                clauses.add(tuple(sorted(set(clause), key=lambda x: (abs(x), x))))
    return tuple(sorted(clauses, key=lambda c: (len(c), c)))


def enumerate_cnf_models(
    clauses: tuple[tuple[int, ...], ...], variable_count: int
) -> tuple[int, ...]:
    """Enumerate every model of a small CNF with deterministic DPLL."""

    assignment = [-1] * variable_count
    models: list[int] = []

    def propagate() -> tuple[bool, list[int]]:
        changed_variables: list[int] = []
        while True:
            changed = False
            for clause in clauses:
                satisfied = False
                undecided: list[int] = []
                for lit in clause:
                    var = abs(lit) - 1
                    value = assignment[var]
                    if value < 0:
                        undecided.append(lit)
                    elif bool(value) == (lit > 0):
                        satisfied = True
                        break
                if satisfied:
                    continue
                if not undecided:
                    return False, changed_variables
                if len(undecided) == 1:
                    lit = undecided[0]
                    var = abs(lit) - 1
                    required = int(lit > 0)
                    if assignment[var] >= 0 and assignment[var] != required:
                        return False, changed_variables
                    if assignment[var] < 0:
                        assignment[var] = required
                        changed_variables.append(var)
                        changed = True
            if not changed:
                return True, changed_variables

    def choose_variable() -> int | None:
        scores = [0] * variable_count
        for clause in clauses:
            if any(
                assignment[abs(lit) - 1] >= 0
                and bool(assignment[abs(lit) - 1]) == (lit > 0)
                for lit in clause
            ):
                continue
            for lit in clause:
                var = abs(lit) - 1
                if assignment[var] < 0:
                    scores[var] += 1
        candidates = [i for i, value in enumerate(assignment) if value < 0]
        if not candidates:
            return None
        return max(candidates, key=lambda i: (scores[i], -i))

    def visit() -> None:
        ok, propagated = propagate()
        if not ok:
            for var in reversed(propagated):
                assignment[var] = -1
            return

        variable = choose_variable()
        if variable is None:
            mask = sum(value << i for i, value in enumerate(assignment))
            models.append(mask)
        else:
            for value in (0, 1):
                assignment[variable] = value
                visit()
            assignment[variable] = -1

        for var in reversed(propagated):
            assignment[var] = -1

    visit()
    return tuple(sorted(set(models)))


def lm_higher_rules() -> tuple[tuple[tuple[int, ...], int], ...]:
    rules: set[tuple[tuple[int, ...], int]] = set()
    for i, j, k, ell in permutations(UNIVERSE):
        raw = (
            ((atom(i, j), atom(k, ell), atom(i, k, (j, ell)), atom(j, ell, (i, k))), atom(i, k)),
            ((atom(i, j), atom(k, ell, (i,)), atom(k, ell, (j,)), atom(i, j, (k, ell))), atom(k, ell)),
            ((atom(i, j), atom(j, ell, (k,)), atom(k, ell, (i,)), atom(i, k, (j, ell))), atom(i, k)),
            ((atom(i, j, (k,)), atom(i, k, (ell,)), atom(i, ell, (j,))), atom(i, j)),
            ((atom(i, j, (k,)), atom(i, k, (ell,)), atom(j, ell, (i,)), atom(k, ell, (j,))), atom(i, j)),
        )
        for premises, conclusion in raw:
            rules.add((tuple(sorted(INDEX[p] for p in set(premises))), INDEX[conclusion]))
    return tuple(sorted(rules))


def satisfies_lm_higher(mask: int) -> bool:
    for premises, conclusion in lm_higher_rules():
        if all(mask >> index & 1 for index in premises) and not mask >> conclusion & 1:
            return False
    return True


def row(mask: int) -> str:
    """Encode membership using the published convention: zero means present."""

    return "".join("0" if mask >> index & 1 else "1" for index in range(len(ATOMS)))


def build_catalogues() -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    all_masks = enumerate_cnf_models(gaussoid_clauses(), len(ATOMS))
    all_rows = tuple(sorted(row(mask) for mask in all_masks))
    t4_rows = tuple(sorted(row(mask) for mask in all_masks if satisfies_lm_higher(mask)))
    excluded = tuple(sorted(set(all_rows) - set(t4_rows)))
    if (len(all_rows), len(t4_rows), len(excluded)) != (679, 629, 50):
        raise ValueError("unexpected four-variable catalogue counts")
    return all_rows, t4_rows, excluded


if __name__ == "__main__":
    gaussoids, regular, excluded = build_catalogues()
    print(
        "catalogue_reconstruction_ok "
        f"G4={len(gaussoids)} T4={len(regular)} excluded={len(excluded)}"
    )
