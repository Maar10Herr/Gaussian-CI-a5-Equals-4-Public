#!/usr/bin/env python3
"""Verify the public-release file manifest and release tree."""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {
    ".git",
    ".venv",
    ".uv-cache",
    ".pytest_cache",
    ".hypothesis",
    ".lake",
    "build",
    "dist",
    "__pycache__",
}
SKIP_FILES = {"MANIFEST.sha256", ".DS_Store"}
GENERATED_CATALOGUE = {
    "data/canonical/G4_bitstrings.txt",
    "data/canonical/T4_bitstrings.txt",
    "data/canonical/T4_excluded_nonrealizable.txt",
}
SHA256 = re.compile(r"[0-9a-f]{64}\Z")


def _included(path: Path) -> bool:
    relative = path.relative_to(ROOT)
    if path.name in SKIP_FILES or path.suffix in {".pyc", ".pyo"}:
        return False
    if any(part in SKIP_DIRS for part in relative.parts):
        return False
    return relative.as_posix() not in GENERATED_CATALOGUE


def _release_files() -> set[str]:
    files = set()
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if any(part in SKIP_DIRS for part in relative.parts):
            continue
        if path.is_symlink():
            raise AssertionError(f"symbolic link is not a release file: {relative}")
        if path.is_file() and _included(path):
            files.add(relative.as_posix())
    return files


def _manifest_entry(raw_path: str) -> tuple[Path, str]:
    relative = Path(raw_path.removeprefix("./"))
    if (
        not raw_path
        or relative.is_absolute()
        or relative == Path(".")
        or ".." in relative.parts
        or any(part in SKIP_DIRS for part in relative.parts)
    ):
        raise AssertionError(f"manifest path is not a safe relative path: {raw_path!r}")
    path = ROOT / relative
    current = ROOT
    for part in relative.parts:
        current /= part
        if current.is_symlink():
            raise AssertionError(f"symbolic link is not a release file: {raw_path}")
    try:
        path.resolve().relative_to(ROOT.resolve())
    except ValueError as error:
        raise AssertionError(f"manifest path escapes repository: {raw_path}") from error
    if not _included(path):
        raise AssertionError(f"manifest entry is not a release file: {raw_path}")
    return path, relative.as_posix()


def main() -> None:
    manifest = ROOT / "MANIFEST.sha256"
    entries = 0
    listed = set()
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            expected, raw_path = line.split("  ", 1)
        except ValueError as error:
            raise AssertionError(f"malformed manifest line: {line!r}") from error
        if not SHA256.fullmatch(expected):
            raise AssertionError(f"invalid SHA-256 digest: {expected!r}")
        path, relative = _manifest_entry(raw_path)
        if not path.is_file():
            raise AssertionError(f"manifest entry is missing: {raw_path}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise AssertionError(f"digest mismatch: {raw_path}")
        if relative in listed:
            raise AssertionError(f"duplicate manifest entry: {raw_path}")
        listed.add(relative)
        entries += 1

    release_files = _release_files()
    unlisted = release_files - listed
    if unlisted:
        raise AssertionError(f"unlisted release files: {sorted(unlisted)}")
    stale = listed - release_files
    if stale:
        raise AssertionError(f"stale manifest entries: {sorted(stale)}")
    print(f"manifest_ok entries={entries}")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as error:
        print(f"manifest verification failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
