#!/usr/bin/env python3
"""Independent, standard-library reconstruction of the T4 catalogue."""

from hashlib import sha256
from pathlib import Path
import runpy

if not __debug__:
    raise SystemExit("verification requires assertions; run Python without -O")

ROOT = Path(__file__).parents[1]
catalogue = runpy.run_path(ROOT / "independent/catalogue.py")
gaussoids, regular, excluded = catalogue["build_catalogues"]()


def digest(rows: tuple[str, ...]) -> str:
    return sha256(("\n".join(rows) + "\n").encode()).hexdigest()


assert (len(gaussoids), len(regular), len(excluded)) == (679, 629, 50)
assert digest(gaussoids) == "94b95946795622fb1a73bc8e0862bf39ce348ccfbc98281fc26e34c3ce45d209"
assert digest(regular) == "37b5b4a718d13213493db45731dd43522378f2951d48151f7de54c0ba7fd8fea"
assert digest(excluded) == "b64b64929590b7c9a01c183b38d334f3679e452ade3b157df9eb4b1d912f6d1d"

print("independent_T4_ok G4=679 T4=629 excluded=50")
