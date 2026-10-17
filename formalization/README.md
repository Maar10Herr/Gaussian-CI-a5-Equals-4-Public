# Partial Lean formalization

This project formalizes parts of the Gaussian conditional-independence argument.
**The full theorem `a_5 = 4` is not yet proved in Lean.** The Python verifier and
all certificates remain part of the paper's verification path.
The formalized semantics use almost-principal minors of positive-definite real
matrices; a probability-library equivalence with Gaussian CI is not developed.

## Established components

- `Cycle.lean` proves the four-premise implication for arbitrary real
  positive-definite five-variable covariance matrices, using almost-principal
  minors. The proof includes correlation bounds, diagonal rescaling, and
  normalization.
- `WorkedWitness.lean` gives a concrete positive-definite rational correlation
  matrix satisfying the three canonical premises and refuting their marginal
  conclusion. Its seven fixed fractions come from certificate 272; the other
  three entries are solved exactly.
- `Minimality.lean` rotates that witness to refute every proper subfamily of
  the four premises. This part does not depend on the unformalized lower bound.
- `FaceWitnesses.lean` proves exact zero and nonzero patterns for ten rational
  positive-definite four-variable matrices. These realize all countermodel
  faces and prove semantic four-local nonderivability without relying on the
  catalogue classification for this countermodel.
- `Finite.lean` and `Generated.lean` check the atom order, symmetry-map count,
  countermodel clauses, supplied catalogue counts and 24-bit bounds, and
  ten-face catalogue membership by kernel reduction. Catalogue row validity,
  distinctness, exhaustive enumeration, and Gaussian realizability are not
  established here. The countermodel's realizability proof is independent of
  that catalogue.
- `Interval.lean` proves real enclosure soundness of rational interval
  arithmetic, polynomial evaluation, and determinant evaluation.
- `PolynomialDerivative.lean` proves symbolic differentiation and interval
  bounds for the Fréchet derivatives of real polynomial systems.
- `Krawczyk.lean` proves an existence-and-uniqueness criterion by Banach
  contraction, with derivative and midpoint-residual bounds. The repository's
  componentwise interval test has not yet been shown to satisfy this criterion.
- `Coverage.lean` proves the logical coverage and threshold assembly lemmas.
  These are conditional theorems: their Gaussian and certificate hypotheses
  have not been discharged for the entire dataset.

The mathematical implication family remains attributed to Šimeček. These files
formalize parts of its proof and the surrounding argument; they do not assert
priority for the family.

## Reproduce

The project pins Lean 4.35.0 and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. From this directory, with that Lean
toolchain available:

```sh
lake update
lake exe cache get
./check.sh
```

`check.sh` builds the library and audits the transitive axiom dependencies of
every exported project theorem. It permits only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; project axioms, `sorryAx`, and native
evaluation oracles cause failure. No Python program is used to accept a Lean
proof. Optional exporters supply data that are then checked by the kernel.

`lake-manifest.json` pins transitive dependency revisions. Neither toolchain
binaries, downloaded libraries, caches, nor compiled proof objects are committed.
The author's local setup is confined to the ignored repository `build/` and
`.lake/` directories.

The project requests one Lean thread and a 2048 MB memory limit per process.
`check.sh` builds project modules sequentially. Populate mathlib's cache first;
building that external library from source can use substantially more resources.
The memory setting is Lean's own limit, not a system-wide cap.

## Remaining proof obligations

See [OBLIGATIONS.md](OBLIGATIONS.md). Remaining obligations include complete
catalogue and closure soundness, real-matrix symmetry and duality, the
proper-support extension, and a proof that all 364 certificate records produce
Gaussian counterexamples with exhaustive representative coverage. The generic
assembly theorem takes these statements as hypotheses.

## Licence and provenance

Original formalization code is distributed under GPL-3.0-or-later in the
[public release](https://github.com/Maar10Herr/Gaussian-CI-a5-Equals-4-Public/blob/main/LICENSE).
Lean and mathlib are external Apache-2.0 dependencies. Generated finite data
come from this repository's axiom-based catalogue builder and public
countermodel. The source and toolchain pins record the formal statements and
their dependencies.
