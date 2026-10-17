# Third-party notices and sources

This repository contains original software, documentation, and proof
certificates by Maarten Linus Herrmann. It does not redistribute third-party
papers, extracted paper text, the gaussoids.de catalogue, selfadhesivity data,
or external source-code repositories.

The theorem and implementation build on published mathematical work cited in
the paper and README. In particular:

- the shared-endpoint implication family is attributed to Petr Šimeček;
- the four-variable classification and higher implication schemes are due to
  Radim Lněnička and František Matúš;
- two-antecedental completeness and selfadhesivity are due to Tobias Boege;
- the interval existence test follows Rudolf Krawczyk and the verification
  framework discussed by Siegfried M. Rump.

`independent/catalogue.py` reconstructs the four-gaussoid catalogue from the
published axiom schemes and records the expected catalogue SHA-256 digests.
The upstream supplemental-material page is
<https://gaussoids.de/gaussoids.html>.

Runtime dependencies are installed from their respective package indexes and
are not vendored. Their licences remain with their authors.

The optional partial formalization pins Lean 4.35.0 and mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Both are external Apache-2.0
dependencies; their sources and compiled caches are not redistributed here.
The formalization's generated finite data come from this repository's
axiom-based enumerator and countermodel.
