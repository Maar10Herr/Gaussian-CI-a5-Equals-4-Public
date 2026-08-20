#!/usr/bin/env python3
"""Write the deterministic public-release SHA-256 manifest."""

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).parents[1]
SKIP_DIRS = {".git", ".venv", ".pytest_cache", ".hypothesis", "build", "dist", "__pycache__"}
SKIP_FILES = {"MANIFEST.sha256", ".DS_Store"}
GENERATED_CATALOGUE = {
    "data/canonical/G4_bitstrings.txt",
    "data/canonical/T4_bitstrings.txt",
    "data/canonical/T4_excluded_nonrealizable.txt",
}


def included(path: Path) -> bool:
    relative = path.relative_to(ROOT)
    if path.name in SKIP_FILES or path.suffix in {".pyc", ".pyo"}:
        return False
    if any(part in SKIP_DIRS for part in relative.parts):
        return False
    return relative.as_posix() not in GENERATED_CATALOGUE


paths = sorted(
    path for path in ROOT.rglob("*") if path.is_file() and included(path)
)
lines = [
    f"{sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT).as_posix()}"
    for path in paths
]
(ROOT / "MANIFEST.sha256").write_text("\n".join(lines) + "\n")
print(f"manifest_written entries={len(lines)}")
