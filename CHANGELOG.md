# Changelog

## Manuscript 0.4 — 2026-10-16

- Publish the concise arXiv manuscript, editable LaTeX, bibliography, and a
  three-file submission archive. The verification implementation and exact
  certificates are unchanged from software release 0.3.1.
- Correct closure-external rule terminology and state the exhaustive-witness
  argument explicitly; retain the mathematical proofs and worked certificate.
- Remove development documentation from the paper and retain replay details
  in the README.
- Remove the author's email and acknowledge Tobias Boege's help with prior
  attribution, terminology, and presentation.

## 0.3.1 — 2026-09-07

- Harden manifest parsing against path traversal, symbolic links, malformed
  digests, duplicate entries, and unlisted release files.
- Make locked test execution explicit and refresh Z3 and Hypothesis.

## 0.3.0 — 2026-08-20

- Publish the version-0.3 preprint and exact certificate set.
- Reconstruct all 679 four-gaussoids directly from the axioms, eliminating the
  need to redistribute the upstream catalogue.
- Verify the 629-model `T4` subset, the four-antecedent countermodel, all 364
  rational Krawczyk certificates, and complete conclusion coverage.
- Add corruption checks, release integrity metadata, citation metadata, and a
  locked development environment.
