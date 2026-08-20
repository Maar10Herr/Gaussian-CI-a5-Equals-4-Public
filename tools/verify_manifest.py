#!/usr/bin/env python3
"""Verify the public-release file manifest."""
from pathlib import Path
import hashlib,sys
R=Path(__file__).parents[1];bad=[];n=0
seen=set()
for line in (R/'MANIFEST.sha256').read_text().splitlines():
 if not line.strip():continue
 sig,rel=line.split('  ',1);p=R/rel;n+=1
 if rel in seen or Path(rel).is_absolute() or '..' in Path(rel).parts:bad.append((rel,'safe unique relative path','INVALID'));continue
 seen.add(rel)
 want=sig;got=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else 'MISSING'
 if got!=want:bad.append((rel,want,got))
if bad:
 for x in bad:print('MISMATCH',*x,file=sys.stderr)
 raise SystemExit(1)
print(f'manifest_ok entries={n}')
