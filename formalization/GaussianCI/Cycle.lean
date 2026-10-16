module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# The five-variable Gaussian cycle implication

The implication family is due to Šimeček. This module checks the direct
correlation-matrix proof used in the manuscript, including the strict correlation
bounds obtained from positive definiteness. It does not establish the separate
four-local countermodel or the three-antecedent lower bound.

Singleton conditional independence is expressed by its almost-principal minor.
For a correlation matrix, `singletonCI R i j k` is `R i j = R i k * R j k`.
The conclusion `marginalCI R i j` is `R i j = 0`.
-/

namespace GaussianCI

open scoped Matrix

/-- The telescoping polynomial identity for the four cycle premises. -/
theorem cycle_telescoping (a b c d p q u s : ℝ) :
    (a - b * p) + p * (b - c * q) + p * q * (c - d * u) +
      p * q * u * (d - a * s) = a * (1 - p * q * u * s) := by
  ring

/-- The scalar cycle argument. Strict factor bounds are hypotheses here; the
correlation-matrix theorem below derives them from positive definiteness. -/
theorem scalar_cycle_implication (a b c d p q u s : ℝ)
    (hp : |p| < 1) (hq : |q| < 1) (hu : |u| < 1) (hs : |s| < 1)
    (h₁ : a - b * p = 0) (h₂ : b - c * q = 0)
    (h₃ : c - d * u = 0) (h₄ : d - a * s = 0) : a = 0 := by
  have hpq : |p * q| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg p, abs_nonneg q]
  have hpqu : |p * q * u| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (p * q), abs_nonneg u]
  have hpqus : |p * q * u * s| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (p * q * u), abs_nonneg s]
  have hfactor : 0 < 1 - p * q * u * s := by
    have := (abs_lt.mp hpqus).2
    linarith
  have hzero := cycle_telescoping a b c d p q u s
  rw [h₁, h₂, h₃, h₄] at hzero
  have : a * (1 - p * q * u * s) = 0 := by simpa using hzero.symm
  exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hfactor)

/-- Every off-diagonal entry of a real positive-definite correlation matrix
has absolute value strictly less than one. The proof uses its principal
two-by-two determinant, not an extra bound hypothesis. -/
theorem correlation_abs_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hR : R.PosDef) (hdiag : ∀ i, R i i = 1)
    {i j : n} (hij : i ≠ j) : |R i j| < 1 := by
  let e : Fin 2 → n := ![i, j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have hdet : 0 < R i i * R j j - R i j * R j i := by
    simpa [Matrix.det_fin_two, Matrix.submatrix, e] using (hR.submatrix he).det_pos
  have hsym : R j i = R i j := by simpa using hR.isHermitian.apply i j
  rw [hdiag i, hdiag j, hsym] at hdet
  apply (sq_lt_one_iff_abs_lt_one (R i j)).mp
  nlinarith

/-- The singleton almost-principal-minor equation defining Gaussian CI. -/
def singletonCI {n : Type*} (R : Matrix n n ℝ) (i j k : n) : Prop :=
  R i j * R k k - R i k * R j k = 0

/-- On a real Hermitian matrix, `singletonCI` is exactly the vanishing
two-by-two almost-principal determinant with row labels `[i,k]` and column
labels `[j,k]`. Positive-definite covariance matrices are Hermitian. -/
theorem singletonCI_iff_almostPrincipalMinor {n : Type*}
    (R : Matrix n n ℝ) (hR : R.IsHermitian) (i j k : n) :
    singletonCI R i j k ↔ (R.submatrix ![i, k] ![j, k]).det = 0 := by
  have hsym : R k j = R j k := by simpa using hR.apply j k
  simp [singletonCI, Matrix.det_fin_two, Matrix.submatrix, hsym]

/-- The unconditioned covariance equation defining Gaussian CI. -/
def marginalCI {n : Type*} (R : Matrix n n ℝ) (i j : n) : Prop := R i j = 0

/-- Gaussian validity of the five-variable cycle, in the covariance-minor
semantics of a positive-definite correlation matrix. The `Fin 5` indices
`0,1,2,3,4` correspond to the manuscript's labels `1,2,3,4,5`.

This proves the analytic-validity component of the upper bound; it does not
claim four-local nonderivability or premise minimality. -/
theorem gaussian_five_cycle {R : Matrix (Fin 5) (Fin 5) ℝ}
    (hR : R.PosDef) (hdiag : ∀ i, R i i = 1)
    (h₁ : singletonCI R 0 1 2) (h₂ : singletonCI R 0 2 3)
    (h₃ : singletonCI R 0 3 4) (h₄ : singletonCI R 0 4 1) :
    marginalCI R 0 1 := by
  have hsym : R 4 1 = R 1 4 := by simpa using hR.isHermitian.apply 1 4
  apply scalar_cycle_implication (R 0 1) (R 0 2) (R 0 3) (R 0 4)
      (R 1 2) (R 2 3) (R 3 4) (R 1 4)
  · exact correlation_abs_lt_one hR hdiag (by decide)
  · exact correlation_abs_lt_one hR hdiag (by decide)
  · exact correlation_abs_lt_one hR hdiag (by decide)
  · exact correlation_abs_lt_one hR hdiag (by decide)
  · simpa [singletonCI, hdiag] using h₁
  · simpa [singletonCI, hdiag] using h₂
  · simpa [singletonCI, hdiag] using h₃
  · simpa [singletonCI, hdiag, hsym] using h₄

/-- Rescale covariance coordinates by a real diagonal matrix. -/
def diagonalRescale {n : Type*} (d : n → ℝ) (S : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => d i * S i j * d j

/-- Invertible real diagonal rescaling preserves positive definiteness. -/
theorem posDef_diagonalRescale {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosDef) (d : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (diagonalRescale d S).PosDef := by
  let D : Matrix n n ℝ := Matrix.diagonal d
  have hinj : Function.Injective D.mulVec := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (hd i) hi
  have heq : Dᴴ * S * D = diagonalRescale d S := by
    ext i j
    simp [D, diagonalRescale, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [← heq]
  exact hS.conjTranspose_mul_mul_same hinj

/-- Singleton CI zero minors are invariant under invertible diagonal scaling. -/
theorem singletonCI_diagonalRescale_iff {n : Type*}
    (S : Matrix n n ℝ) (d : n → ℝ) (hd : ∀ i, d i ≠ 0) (i j k : n) :
    singletonCI (diagonalRescale d S) i j k ↔ singletonCI S i j k := by
  have hfactor : d i * d j * d k ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hd i) (hd j)) (pow_ne_zero _ (hd k))
  have hid : (d i * S i j * d j) * (d k * S k k * d k) -
      (d i * S i k * d k) * (d j * S j k * d k) =
      (d i * d j * d k ^ 2) * (S i j * S k k - S i k * S j k) := by ring
  simp only [singletonCI, diagonalRescale]
  rw [hid, mul_eq_zero]
  simp [hfactor]

/-- Marginal CI zero covariances are invariant under invertible diagonal scaling. -/
theorem marginalCI_diagonalRescale_iff {n : Type*}
    (S : Matrix n n ℝ) (d : n → ℝ) (hd : ∀ i, d i ≠ 0) (i j : n) :
    marginalCI (diagonalRescale d S) i j ↔ marginalCI S i j := by
  simp [marginalCI, diagonalRescale, mul_eq_zero, hd]

/-- Normalize a covariance matrix by its coordinate standard deviations. -/
noncomputable def correlationNormalize {n : Type*} (S : Matrix n n ℝ) : Matrix n n ℝ :=
  diagonalRescale (fun i => (Real.sqrt (S i i))⁻¹) S

/-- Positive-definite covariance matrices normalize to correlation matrices. -/
theorem correlationNormalize_posDef_diag {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    (correlationNormalize S).PosDef ∧ ∀ i, correlationNormalize S i i = 1 := by
  have hsqrt : ∀ i, Real.sqrt (S i i) ≠ 0 :=
    fun i => ne_of_gt (Real.sqrt_pos.mpr (hS.diag_pos (i := i)))
  constructor
  · exact posDef_diagonalRescale hS _ (fun i => inv_ne_zero (hsqrt i))
  · intro i
    change (Real.sqrt (S i i))⁻¹ * S i i * (Real.sqrt (S i i))⁻¹ = 1
    calc
      _ = (Real.sqrt (S i i))⁻¹ *
          (Real.sqrt (S i i) * Real.sqrt (S i i)) * (Real.sqrt (S i i))⁻¹ := by
        rw [Real.mul_self_sqrt (hS.diag_pos (i := i)).le]
      _ = 1 := by field_simp [hsqrt i]

/-- The five-cycle implication for every real positive-definite covariance
matrix. Normalization and invariance of the relevant CI minors are proved above,
so this theorem has no separate correlation-normalization hypothesis. -/
theorem gaussian_five_cycle_covariance {S : Matrix (Fin 5) (Fin 5) ℝ}
    (hS : S.PosDef)
    (h₁ : singletonCI S 0 1 2) (h₂ : singletonCI S 0 2 3)
    (h₃ : singletonCI S 0 3 4) (h₄ : singletonCI S 0 4 1) :
    marginalCI S 0 1 := by
  let d : Fin 5 → ℝ := fun i => (Real.sqrt (S i i))⁻¹
  have hd : ∀ i, d i ≠ 0 := fun i =>
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hS.diag_pos (i := i))))
  obtain ⟨hR, hdiag⟩ := correlationNormalize_posDef_diag hS
  have hc₁ : singletonCI (correlationNormalize S) 0 1 2 :=
    (singletonCI_diagonalRescale_iff S d hd 0 1 2).mpr h₁
  have hc₂ : singletonCI (correlationNormalize S) 0 2 3 :=
    (singletonCI_diagonalRescale_iff S d hd 0 2 3).mpr h₂
  have hc₃ : singletonCI (correlationNormalize S) 0 3 4 :=
    (singletonCI_diagonalRescale_iff S d hd 0 3 4).mpr h₃
  have hc₄ : singletonCI (correlationNormalize S) 0 4 1 :=
    (singletonCI_diagonalRescale_iff S d hd 0 4 1).mpr h₄
  exact (marginalCI_diagonalRescale_iff S d hd 0 1).mp
    (gaussian_five_cycle hR hdiag hc₁ hc₂ hc₃ hc₄)

#print axioms cycle_telescoping
#print axioms scalar_cycle_implication
#print axioms correlation_abs_lt_one
#print axioms singletonCI_iff_almostPrincipalMinor
#print axioms gaussian_five_cycle
#print axioms posDef_diagonalRescale
#print axioms singletonCI_diagonalRescale_iff
#print axioms marginalCI_diagonalRescale_iff
#print axioms correlationNormalize_posDef_diag
#print axioms gaussian_five_cycle_covariance

end GaussianCI
