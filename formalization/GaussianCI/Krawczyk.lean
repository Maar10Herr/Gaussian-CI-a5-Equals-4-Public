module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Root existence for preconditioned certificate systems

The results below prove existence and uniqueness of a real zero from Banach
contraction hypotheses.  In particular the closed-ball criterion derives both
self-mapping and contraction from a residual bound and a derivative bound.

The repository's rational interval evaluator and componentwise Krawczyk test
have not yet been proved to provide these hypotheses.  No theorem here asserts
that any of the 364 certificate records passes this criterion.
-/

namespace GaussianCI

open Function
open scoped NNReal

section CompleteNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed-point map used by preconditioned root certificates. -/
def preconditionedMap (F : E → E) (C : E →L[ℝ] E) (x : E) : E := x - C (F x)

/-- With an injective preconditioner, fixed points are exactly roots. -/
theorem preconditionedMap_fixed_iff {F : E → E} {C : E →L[ℝ] E}
    (hC : Function.Injective C) (x : E) :
    preconditionedMap F C x = x ↔ F x = 0 := by
  constructor
  · intro hfixed
    have hzero : C (F x) = 0 := sub_eq_self.mp hfixed
    apply hC
    simpa using hzero
  · intro hroot
    simp [preconditionedMap, hroot]

/-- Banach's theorem gives a unique zero on any nonempty closed invariant domain. -/
theorem exists_zero_of_contracting_preconditionedMap [CompleteSpace E]
    {F : E → E} {C : E →L[ℝ] E} {domain : Set E} {q : ℝ≥0}
    (hC : Function.Injective C) (hclosed : IsClosed domain)
    (hnonempty : domain.Nonempty)
    (hmaps : Set.MapsTo (preconditionedMap F C) domain domain)
    (hq : q < 1) (hlipschitz : LipschitzOnWith q (preconditionedMap F C) domain) :
    ∃ root ∈ domain, F root = 0 ∧ ∀ other ∈ domain, F other = 0 → other = root := by
  classical
  have hcontract : ContractingWith q (hmaps.restrict (preconditionedMap F C) domain domain) :=
    ⟨hq, hlipschitz.mapsToRestrict hmaps⟩
  obtain ⟨initial, hinitial⟩ := hnonempty
  obtain ⟨root, hroot_mem, hfixed, _, _⟩ :=
    ContractingWith.exists_fixedPoint' hclosed.isComplete hmaps hcontract hinitial
      (edist_ne_top initial (preconditionedMap F C initial))
  have hroot : F root = 0 := (preconditionedMap_fixed_iff hC root).mp hfixed
  refine ⟨root, hroot_mem, hroot, ?_⟩
  intro other hother_mem hother
  have hother_fixed : preconditionedMap F C other = other :=
    (preconditionedMap_fixed_iff hC other).mpr hother
  have hroot_subtype : IsFixedPt
      (hmaps.restrict (preconditionedMap F C) domain domain) ⟨root, hroot_mem⟩ :=
    Subtype.ext hfixed
  have hother_subtype : IsFixedPt
      (hmaps.restrict (preconditionedMap F C) domain domain) ⟨other, hother_mem⟩ :=
    Subtype.ext hother_fixed
  exact congrArg Subtype.val (hcontract.fixedPoint_unique' hother_subtype hroot_subtype)

/-- A derivative enclosure for `I - C F'` provides the required contraction. -/
theorem preconditionedMap_lipschitz_of_derivative_bound
    {F : E → E} {C : E →L[ℝ] E} {domain : Set E}
    {J : E → E →L[ℝ] E} {q : ℝ≥0}
    (hconvex : Convex ℝ domain)
    (hderiv : ∀ x ∈ domain, HasFDerivAt F (J x) x)
    (hbound : ∀ x ∈ domain, ‖ContinuousLinearMap.id ℝ E - C.comp (J x)‖₊ ≤ q) :
    LipschitzOnWith q (preconditionedMap F C) domain := by
  apply hconvex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le _ hbound
  intro x hx
  exact ((hasFDerivAt_id x).sub
    (C.hasFDerivAt.comp x (hderiv x hx))).hasFDerivWithinAt

/-- The derivative bound is sufficient on any closed convex invariant domain. -/
theorem exists_unique_zero_of_preconditioned_derivative_bound [CompleteSpace E]
    {F : E → E} {C : E →L[ℝ] E} {domain : Set E}
    {J : E → E →L[ℝ] E} {q : ℝ≥0}
    (hC : Function.Injective C) (hclosed : IsClosed domain)
    (hnonempty : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hmaps : Set.MapsTo (preconditionedMap F C) domain domain) (hq : q < 1)
    (hderiv : ∀ x ∈ domain, HasFDerivAt F (J x) x)
    (hbound : ∀ x ∈ domain, ‖ContinuousLinearMap.id ℝ E - C.comp (J x)‖₊ ≤ q) :
    ∃ root ∈ domain, F root = 0 ∧ ∀ other ∈ domain, F other = 0 → other = root :=
  exists_zero_of_contracting_preconditionedMap hC hclosed hnonempty hmaps hq
    (preconditionedMap_lipschitz_of_derivative_bound hconvex hderiv hbound)

/-- A residual bound and contraction estimate make a closed ball invariant. -/
theorem preconditionedMap_mapsTo_closedBall_of_residual_bound
    {F : E → E} {C : E →L[ℝ] E} {center : E} {radius : ℝ} {q : ℝ≥0}
    (hradius : 0 ≤ radius)
    (hlipschitz : LipschitzOnWith q (preconditionedMap F C) (Metric.closedBall center radius))
    (hresidual : ‖C (F center)‖ ≤ (1 - (q : ℝ)) * radius) :
    Set.MapsTo (preconditionedMap F C)
      (Metric.closedBall center radius) (Metric.closedBall center radius) := by
  intro x hx
  have hcenter : center ∈ Metric.closedBall center radius :=
    Metric.mem_closedBall_self hradius
  have hdistance : dist (preconditionedMap F C center) center = ‖C (F center)‖ := by
    simp [preconditionedMap]
  have hnear : dist x center ≤ radius := Metric.mem_closedBall.mp hx
  apply Metric.mem_closedBall.mpr
  calc
    dist (preconditionedMap F C x) center ≤
        dist (preconditionedMap F C x) (preconditionedMap F C center) +
          dist (preconditionedMap F C center) center := dist_triangle _ _ _
    _ ≤ (q : ℝ) * dist x center + ‖C (F center)‖ :=
      add_le_add (hlipschitz.dist_le_mul x hx center hcenter) hdistance.le
    _ ≤ (q : ℝ) * radius + (1 - (q : ℝ)) * radius :=
      add_le_add (mul_le_mul_of_nonneg_left hnear q.coe_nonneg) hresidual
    _ = radius := by ring

/--
A concrete analytic sufficient criterion for an interval root certificate.
The hypotheses bound the preconditioned derivative and midpoint residual; they
do not assume a root, a self-map, or a Lipschitz estimate.
-/
theorem exists_unique_zero_closedBall_of_preconditioned_derivative_bound [CompleteSpace E]
    {F : E → E} {C : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    {center : E} {radius : ℝ} {q : ℝ≥0}
    (hC : Function.Injective C) (hradius : 0 ≤ radius) (hq : q < 1)
    (hderiv : ∀ x ∈ Metric.closedBall center radius, HasFDerivAt F (J x) x)
    (hbound : ∀ x ∈ Metric.closedBall center radius,
      ‖ContinuousLinearMap.id ℝ E - C.comp (J x)‖₊ ≤ q)
    (hresidual : ‖C (F center)‖ ≤ (1 - (q : ℝ)) * radius) :
    ∃ root ∈ Metric.closedBall center radius,
      F root = 0 ∧ ∀ other ∈ Metric.closedBall center radius, F other = 0 → other = root := by
  have hlipschitz : LipschitzOnWith q (preconditionedMap F C)
      (Metric.closedBall center radius) :=
    preconditionedMap_lipschitz_of_derivative_bound (convex_closedBall center radius) hderiv hbound
  exact exists_zero_of_contracting_preconditionedMap hC Metric.isClosed_closedBall
    ⟨center, Metric.mem_closedBall_self hradius⟩
    (preconditionedMap_mapsTo_closedBall_of_residual_bound hradius hlipschitz hresidual)
    hq hlipschitz

#print axioms preconditionedMap_fixed_iff
#print axioms exists_zero_of_contracting_preconditionedMap
#print axioms preconditionedMap_lipschitz_of_derivative_bound
#print axioms exists_unique_zero_of_preconditioned_derivative_bound
#print axioms exists_unique_zero_closedBall_of_preconditioned_derivative_bound

end CompleteNormedSpace

end GaussianCI
