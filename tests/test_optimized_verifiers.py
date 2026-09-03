from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).parents[1]
ASSERTION_DEPENDENT_SCRIPTS = (
    "independent/verify_corruptions.py",
    "independent/verify_cycle_rule.py",
    "independent/verify_m3_classification.py",
    "independent/verify_t4.py",
    "tools/reproduce_small_n.py",
)


@pytest.mark.parametrize("script", ASSERTION_DEPENDENT_SCRIPTS)
def test_assertion_dependent_scripts_reject_optimized_python(script: str) -> None:
    result = subprocess.run(
        [sys.executable, "-O", ROOT / script],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "requires assertions" in result.stderr
