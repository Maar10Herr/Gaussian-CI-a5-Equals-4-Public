#!/usr/bin/env python3
"""Materialize the self-reconstructed four-variable catalogues."""
from pathlib import Path
import runpy
R=Path(__file__).parents[1]
rows,keep,drop=runpy.run_path(R/'independent/catalogue.py')['build_catalogues']()
out=R/'data/canonical'; out.mkdir(parents=True,exist_ok=True)
(out/'G4_bitstrings.txt').write_text('\n'.join(rows)+'\n')
(out/'T4_bitstrings.txt').write_text('\n'.join(keep)+'\n')
(out/'T4_excluded_nonrealizable.txt').write_text('\n'.join(drop)+'\n')
print(f'G4=679 T4=629 excluded=50')
