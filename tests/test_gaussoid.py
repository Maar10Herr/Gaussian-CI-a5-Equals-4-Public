from pathlib import Path
import runpy
from five_gaussian_ci.atoms import atoms
from five_gaussian_ci.gaussoid import *
ROOT=Path(__file__).parents[1]

def test_three_variable_baseline_exhaustive():
    A=atoms((1,2,3)); good=[]
    for mask in range(1<<6):
        S=frozenset(a for i,a in enumerate(A) if mask&(1<<i))
        if is_gaussoid(S,(1,2,3)): good.append(S)
    assert len(good)==11

def test_four_variable_catalogue_and_exact_T4():
    rows, expected_t4, excluded = runpy.run_path(
        ROOT/'independent/catalogue.py'
    )['build_catalogues']()
    G=[decode_zero_means_member(r,(1,2,3,4)) for r in rows]
    assert len(G)==679 and len(set(G))==679
    assert all(is_gaussoid(s,(1,2,3,4)) for s in G)
    T4=[s for s in G if satisfies_lm_higher_4(s)]
    assert len(T4)==629
    assert len(expected_t4)==629 and len(excluded)==50

def test_lm_rule_template_counts():
    rules=lm_higher_rules_4()
    assert rules and {len(p) for p,_ in rules}=={3,4}
