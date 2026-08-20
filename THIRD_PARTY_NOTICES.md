# Third-party notices and scholarly inputs

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
published axiom schemes. Its expected SHA-256 values are recorded as factual
integrity identifiers. The upstream supplemental-material page is
<https://gaussoids.de/gaussoids.html>.

Runtime dependencies are installed from their respective package indexes and
are not vendored. Their licences remain with their authors.
