from fractions import Fraction as F
from pathlib import Path
import copy,json
from five_gaussian_ci.interval_cert import *
def test_interval_arithmetic_contains_endpoints():
 assert mul((F(-2),F(3)),(F(-4),F(5)))==(F(-12),F(15))
 assert det_interval([[I(2),I(1)],[I(1),I(3)]])==(F(5),F(5))

def test_real_certificate_and_corrupted_preconditioner():
 root=Path(__file__).parents[1]
 c=json.loads((root/'certificates/m3_interval_certificates.json').read_text())['certificates'][0]
 assert verify_witness(c)==(True,'ok')
 bad=copy.deepcopy(c);bad['C']=[[[0,1]]*3 for _ in range(3)]
 assert verify_witness(bad)[0] is False
