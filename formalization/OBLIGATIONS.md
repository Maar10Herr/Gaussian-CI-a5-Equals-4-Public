# Gaussian CI formalization: remaining mathematical obligations

This document lists the established Lean theorems and the conditions required
for a complete formal proof of the manuscript's claim `a_5 = 4`. Hypotheses about
Gaussian validity, closure soundness, and certificate soundness must still be
instantiated for the repository data.

## Logical assembly

`GaussianCI/Coverage.lean` defines semantic validity for a family of sets of CI
atoms, semantic counterexamples, simultaneous witness coverage, sound closure,
premise minimality, and the threshold as a least antecedent count. Its conditional
theorems establish:

- A sound inference step remains sound after any finite number of iterations.
- Exact finite coverage of the complement of a closure gives a counterexample to
  each omitted conclusion, provided every certificate has a semantic witness.
- Such coverage forces each Gaussian-valid conclusion into the sound local
  closure and therefore makes the rule local.
- If Gaussian models belong to the local model family, valid conclusions are
  exactly the computed closure on any premise set satisfying these conditions.
- A checked extension from smaller premise sets to three-premise sets transfers
  counterexamples back to the smaller sets.
- Locality of all valid rules with at most three premises, combined with a valid
  nonlocal four-premise rule, gives premise minimality and least count four.

Their remaining hypotheses concern the Gaussian model family, catalogue
validity, interval certificates, and coverage for the repository's certificate
file.

## Obligation map for the complete result

| Domain | Required mathematical statement | Existing evidence and remaining formal work |
| --- | --- | --- |
| Atoms and encoding | Elementary atoms have distinct endpoints, a disjoint conditioning set, and an unambiguous finite index; five labels give 80 atoms. | Python rebuilds the order. Lean finite checks must connect index operations to this semantic atom type, including the 24-atom face order. |
| Gaussian semantics | An atom holds precisely when its almost-principal minor vanishes for a symmetric positive-definite real covariance matrix. | Manuscript uses the standard Gaussian equivalence. A matrix-based Lean statement can avoid developing probability theory, but must name this scope accurately. |
| Upper-bound validity | The four singleton-conditioned premises force the unconditional conclusion for every positive-definite covariance matrix. | Proved in `Cycle.lean`, including almost-principal-minor semantics, strict correlation bounds, normalization, and rescaling invariance. |
| Local model family | `T4` means that every marginal and conditional four-face is Gaussian realizable. | The relation between Gaussian realizability and the bit predicate encoding the gaussoid axioms plus five higher implications requires proof. |
| Four-variable catalogue | The enumerator includes every relevant four-variable structure; each accepted row used as a face is Gaussian realizable. | Python exhaustively enumerates 679 axiom models and filters to 629. Its identification with Gaussian structures currently invokes Lnenicka–Matus. Reprove that classification, or prove the smaller soundness and realization statements described below. |
| Countermodel nonlocality | The printed 80-bit model satisfies all four premises, omits the conclusion, and has ten Gaussian-realizable four-faces. | Proved in `Finite.lean` and `FaceWitnesses.lean`. Ten exact rational positive-definite matrices realize the complete face patterns, giving semantic nonlocality without the 629-model classification. |
| Closure soundness | Each face-intersection update preserves every compatible semantic `T4` model. | The generic iteration theorem is proved. The concrete step needs complete catalogue enumeration and the implication from semantic face realizability to catalogue membership. |
| Symmetry | Label permutations and duality preserve Gaussian validity and `T4`, and every three-premise set maps to a representative. | Finite maps are reconstructible; determinant relabeling and inversion/duality require real-matrix proofs. Duality uses Jacobi's complementary-minor identity. Support is not invariant under duality. |
| Rational intervals | Interval operations enclose the corresponding real operation; determinant and derivative evaluators are sound. | Proved for interval arithmetic, polynomial expressions, determinants with complete enumeration lists, and Fréchet derivatives of polynomial systems in `Interval.lean` and `PolynomialDerivative.lean`. Instantiating these evaluators on every certificate remains. |
| Krawczyk existence | The accepted interval condition gives a real zero of the three premise polynomials inside the box. | `Krawczyk.lean` proves existence and uniqueness of a real zero from derivative and residual bounds by contraction. Deriving those bounds from the componentwise rational-box check remains. |
| Positive definiteness | Positive lower bounds for all leading principal minors imply the witness matrix is positive definite. | Requires the real Sylvester criterion and determinant enclosure correctness. |
| False conclusions | Every atom in a certificate's cover list has a nonzero almost-principal minor at its real root. | Follows from interval exclusion once evaluation soundness and root existence are established. |
| Full-support coverage | Each of 335 representatives is covered on all 80 atoms outside its sound closure. | There are 364 existing certificates. Counts such as 21,167 alone are insufficient; the set equality is needed separately for every representative. |
| Proper-support cases | Premises using a proper label subset have a positive-definite extension violating every proposed conclusion involving an outside label; conclusions inside that subset are local. | The manuscript proves a generic polynomial-avoidance argument. Formalization needs polynomial nonidentity, positivity near identity, and avoiding finitely many zero loci. Alternatively, supply finite exact witness certificates for the 104 representative cases. |
| Zero through two premises | Every Gaussian-valid rule with at most two antecedents is local. | The paper invokes Boege's corrected theorem. A bounded finite-padding alternative using the existing three-premise classification passed exploratory exact checks; its concrete padding relation still needs Lean verification. |
| Final threshold | The valid, nonlocal four-premise rule and the lower bound yield `a_5 = 4`, with premise minimality and full support. | Generic conditional assembly is proved in `Coverage.lean`; its Gaussian hypotheses remain to be instantiated for the repository data. |

The concrete four-premise rule's premise minimality is proved separately in
`Minimality.lean`: rotations of the exact worked witness refute every proper
subfamily. `WorkedWitness.lean` establishes the underlying positive-definite
matrix, its three CI equations, and the false marginal conclusion directly.

## Reducing external theorem dependencies

### Four-variable classification

A complete formalization can avoid reproducing every part of the published
629-model realizability classification. For the lower-bound closure, it is
sufficient to prove that every Gaussian four-face satisfies all encoded rules
and that enumeration includes every model of those rules. The closure then
uses an outer approximation, which is sound. For the upper-bound countermodel,
exact rational positive-definite covariance witnesses for its ten four-faces
prove their realizability directly. `FaceWitnesses.lean` proves these ten
realizability statements. Gaussian-rule soundness and enumeration completeness
for the lower-bound closure remain unproved.

### Rules with fewer than three premises

For each premise set `P` of size at most two and conclusion outside `C(P)`, find a
three-element superset `Q` with that conclusion outside `C(Q)`. A Gaussian
counterexample to `Q` also satisfies `P`. This uses existing three-premise results
and needs no new numerical witness boxes.

An exact exploratory check against the current Python closure succeeded on all
symmetry representatives: one zero-premise orbit, two one-premise orbits, and
32 two-premise orbits. After discarding redundant choices, four triple supersets
sufficed for the empty set, three for each singleton representative, and at most
two for each pair representative. This is finite Python evidence, not a Lean
proof of the concrete extension relation. The generic transfer lemma is proved.

## Requirements for a complete proof

A final Lean theorem must derive the matrix statement from checked data and
proved mathematical facts. It must not add the desired result or unresolved
analytic steps as axioms. No `sorry`, `admit`, custom `axiom`, or `native_decide`
may be used to declare the concrete certificate checks correct. Generated
certificate data and Python search programs can remain untrusted inputs to
kernel-checked proof construction. Standard Lean foundational axioms reported
by `#print axioms` are distinct from project-specific unproved assumptions.

## Root-existence theorem for preconditioned systems

`GaussianCI/Krawczyk.lean` proves the following analytic implications in a
complete real normed vector space. A fixed point of `T(x) = x - C(F(x))` is a zero
of `F` when the continuous linear preconditioner `C` is injective. Banach's theorem
then gives a unique zero on any nonempty closed domain that `T` preserves
and on which it is a strict contraction. A bound on the operator norm of
`I - C ∘ J(x)`, where `J(x)` is a proved derivative of `F`, supplies the contraction
through the mean-value theorem on a convex domain.

A sufficient criterion for a closed ball also derives invariance:
if `0 ≤ r`, `q < 1`, the preconditioned derivative has operator norm at most `q`
throughout the ball of center `m` and radius `r`, and
`‖C(F(m))‖ ≤ (1 - q) r`, then `F` has exactly one zero in that ball. The criterion
does not assume a root, a self-map, or a Lipschitz estimate.

`Krawczyk.lean` proves these analytic criteria. Formal verification of the
repository's Krawczyk certificates still requires the following statements:

- Instantiate the proved polynomial derivative evaluator on the concrete
  almost-principal polynomial systems.
- Convert the proved interval Jacobian entry enclosures into the required real
  operator-norm bounds.
- Derive box invariance and a strict contraction in the appropriate weighted
  sup norm from componentwise strict Krawczyk inclusion, or independently verify
  the sufficient closed-ball bounds above for each record.
- Prove that nonsingularity of each rational matrix record gives injectivity of
  its real continuous linear map.
- Check the resulting hypotheses for each of the 364 certificate records.

The closed-ball residual criterion is sufficient and can require stronger
bounds than the paper's componentwise interval test.
