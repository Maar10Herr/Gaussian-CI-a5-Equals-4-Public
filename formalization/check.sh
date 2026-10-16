#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "$0")" && pwd -P)"
cd "$project_dir"
# Build project modules in dependency order to avoid concurrent proof jobs.
# mathlib's downloaded cache should be populated before running this script.
for module in Cycle WorkedWitness Minimality Finite Generated FaceWitnesses \
  Interval PolynomialDerivative Krawczyk Coverage; do
  lake build "GaussianCI.$module"
done
lake build GaussianCI
lake build GaussianCI.Audit
lake env lean -j1 -M2048 GaussianCI/Audit.lean
