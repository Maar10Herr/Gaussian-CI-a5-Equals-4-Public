from pathlib import Path
import runpy
import pytest
from five_gaussian_ci.atoms import atoms
from five_gaussian_ci.orbits import *
from five_gaussian_ci.local_theory import T4MinorTheory,T4ArcTheory
R=Path(__file__).parents[1]

def test_symmetry_group_and_rule_canonicalization():
 m=symmetry_maps(range(1,6)); assert len(m)==240 and all(len(set(g))==80 for g in m)
 p=(0,1,8); k=canonical_rule(p,17,m)
 assert all(k <= canonical_rule(p,17,(g,)) for g in m)

def test_t4_minor_theory_obvious_consequences(tmp_path):
 rows=runpy.run_path(R/'independent/catalogue.py')['build_catalogues']()[1]
 catalogue=tmp_path/'T4_bitstrings.txt'
 catalogue.write_text('\n'.join(rows)+'\n')
 T=T4MinorTheory(catalogue)
 # LM(20): (12|3),(13|4),(14|2) => (12|), lifted on labels 1..4.
 A=atoms(range(1,6)); idx={a:i for i,a in enumerate(A)}
 from five_gaussian_ci.atoms import Atom
 P=[idx[Atom(1,2,frozenset({3}))],idx[Atom(1,3,frozenset({4}))],idx[Atom(1,4,frozenset({2}))]]
 c=idx[Atom(1,2)]
 assert c in T.consequences(P)
 assert T.consequences(P)==T4ArcTheory(catalogue).consequences(P)

def test_t4_theories_reject_malformed_catalogues(tmp_path):
 malformed=tmp_path/'malformed.txt'
 malformed.write_text(('0'*24+'\n')*629)
 with pytest.raises(ValueError):
  T4ArcTheory(malformed)
 with pytest.raises(ValueError):
  T4MinorTheory(malformed)
