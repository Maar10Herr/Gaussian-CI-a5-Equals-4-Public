#!/usr/bin/env python3
"""Dependency-free deliberate-corruption checks for exact proof objects."""

if not __debug__:
    raise SystemExit("verification requires assertions; run Python without -O")

from pathlib import Path
import copy,hashlib,importlib.util,json
R=Path(__file__).parents[1]

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,R/path)
 if spec is None or spec.loader is None:raise RuntimeError(path)
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

# 1. A singular/zero Krawczyk preconditioner must be rejected.
v=load('verify_m3_module','independent/verify_m3_classification.py')
D=json.loads((R/'certificates/m3_interval_certificates.json').read_text())
bad=copy.deepcopy(D['certificates'][0]);bad['C']=[[[0,1]]*3 for _ in range(3)]
assert not v.verify_cert(bad)

# 2. The full cycle checker must reject a present conclusion.
cyc=load('verify_cycle_module','independent/verify_cycle_rule.py')
bits=(R/'certificates/cycle_rule_t4_countermodel.txt').read_text().strip();assert bits[0]=='0'
tampered='1'+bits[1:];assert not cyc.check_countermodel(tampered)

# 3. It must also reject at least one nontrivial internal bit flip through the
# gaussoid/face checks, not merely through the premise/conclusion gate.
internal_rejection=False
for k in range(80):
 if k in ({0}|set(cyc.prem)):continue
 z=bits[:k]+('0' if bits[k]=='1' else '1')+bits[k+1:]
 if not cyc.check_countermodel(z):internal_rejection=True;break
assert internal_rejection

# 4. Altering any manifested byte must change its pinned SHA-256.
p=R/'certificates/cycle_rule_t4_countermodel.txt';raw=p.read_bytes();record=None
for line in (R/'MANIFEST.sha256').read_text().splitlines():
 if line.endswith('  certificates/cycle_rule_t4_countermodel.txt'):record=line.split('  ',1)[0];break
assert record and hashlib.sha256(raw).hexdigest()==record
assert hashlib.sha256(raw+b'corruption').hexdigest()!=record
print('corruption_checks_ok cases=4')
