#!/usr/bin/env python3
"""Exact small-n baseline reproducer."""

if not __debug__:
    raise SystemExit("reproduction requires assertions; run Python without -O")

from pathlib import Path
import runpy
from five_gaussian_ci.atoms import atoms
from five_gaussian_ci.gaussoid import is_gaussoid
assert [len(atoms(range(1,n+1))) for n in (1,2,3,4,5)] == [0,1,6,24,80]
A=atoms((1,2,3))
T3=[]
for mask in range(1<<len(A)):
 S=frozenset(a for q,a in enumerate(A) if mask&(1<<q))
 if is_gaussoid(S,(1,2,3)): T3.append(S)
assert len(T3)==11
R=Path(__file__).parents[1]
rows,T4,excluded=runpy.run_path(R/'independent/catalogue.py')['build_catalogues']()
assert (len(rows),len(T4),len(excluded))==(679,629,50)
print('atoms=(0,1,6,24,80) regular_gaussian_structures=(1,2,11,629) G4=679')
