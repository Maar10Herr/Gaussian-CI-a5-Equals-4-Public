PYTHON := python3
COREPY := env PYTHONNOUSERSITE=1 $(PYTHON) -I

.PHONY: test baselines catalogue materialize-catalogue m3 cycle corruptions manifest verify-core verify build clean

test:
	uv run --frozen --extra test pytest -q

baselines:
	uv run --frozen python tools/reproduce_small_n.py

catalogue:
	$(COREPY) independent/verify_t4.py

materialize-catalogue:
	uv run python tools/build_t4.py

m3:
	$(COREPY) independent/verify_m3_classification.py

cycle:
	$(COREPY) independent/verify_cycle_rule.py

corruptions:
	$(COREPY) independent/verify_corruptions.py

manifest:
	$(COREPY) tools/verify_manifest.py

verify-core: catalogue m3 cycle corruptions manifest

verify: test baselines verify-core

build:
	uv build

clean:
	rm -rf .pytest_cache .hypothesis build dist
	find src tests tools independent -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f data/canonical/G4_bitstrings.txt data/canonical/T4_bitstrings.txt data/canonical/T4_excluded_nonrealizable.txt
