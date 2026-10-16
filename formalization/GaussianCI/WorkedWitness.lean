module

public import GaussianCI.Cycle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

@[expose] public section

/-!
# An exact Gaussian witness from worked certificate 272

The seven fixed rational entries below are copied from the zero-based entry 272
of `certificates/m3_interval_certificates.json`. For this triangular premise
system the other three entries can be solved exactly over the rationals, without
an interval existence argument. This module proves that the resulting real
correlation matrix is positive definite, satisfies `[12|3]`, `[13|4]`, `[14|5]`,
and violates `[12]`. Indices `0,1,2,3,4` correspond to labels `1,2,3,4,5`.

This is one witness, not the exhaustive lower-bound calculation. The proof does
not use the certificate's reported coverage set or its preconditioner.
-/

namespace GaussianCI

noncomputable section

def witness15 : ℝ := -7512862 / 32408079
def witness23 : ℝ := -5076563 / 95066657
def witness24 : ℝ := 355216 / 2466155
def witness25 : ℝ := -17457127 / 97271260
def witness34 : ℝ := 7894693 / 48443657
def witness35 : ℝ := -14768891 / 57593388
def witness45 : ℝ := 4785782 / 33720645
def witness14 : ℝ := witness15 * witness45
def witness13 : ℝ := witness14 * witness34
def witness12 : ℝ := witness13 * witness23

/-- An exact rational correlation matrix extracted algebraically from the fixed
entries of certificate 272. It uses no rounded displayed decimal entries. -/
def workedWitness : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![1, witness12, witness13, witness14, witness15],
    ![witness12, 1, witness23, witness24, witness25],
    ![witness13, witness23, 1, witness34, witness35],
    ![witness14, witness24, witness34, 1, witness45],
    ![witness15, witness25, witness35, witness45, 1]]

theorem workedWitness_diagonal (i : Fin 5) : workedWitness i i = 1 := by
  fin_cases i <;> rfl

theorem workedWitness_isHermitian : workedWitness.IsHermitian := by
  ext i j
  change star (workedWitness j i) = workedWitness i j
  fin_cases i <;> fin_cases j <;> simp [workedWitness]

/-- Every row has off-diagonal absolute sum strictly below its diagonal entry.
All inequalities are exact rational arithmetic checked in the kernel. -/
theorem workedWitness_row_sum_lt_one (i : Fin 5) :
    (∑ j ∈ Finset.univ.erase i, ‖workedWitness i j‖) < 1 := by
  fin_cases i <;>
    norm_num [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ,
      workedWitness, witness12, witness13, witness14, witness15, witness23,
      witness24, witness25, witness34, witness35, witness45, Real.norm_eq_abs]

/-- A Hermitian real correlation matrix with strict diagonal dominance is
positive definite. Gershgorin places every eigenvalue in a positive interval. -/
theorem posDef_of_diagonal_dominance {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hR : R.IsHermitian) (hdiag : ∀ i, R i i = 1)
    (hrow : ∀ i, (∑ j ∈ Finset.univ.erase i, ‖R i j‖) < 1) : R.PosDef := by
  apply hR.posDef_iff_eigenvalues_pos.mpr
  intro i
  have heigen : Module.End.HasEigenvalue R.toLin' (hR.eigenvalues i) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    exact hR.eigenvalues_mem_spectrum_real i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball heigen
  rw [mem_closedBall_iff_norm', hdiag k, Real.norm_eq_abs] at hk
  have hupper := (abs_le.mp hk).2
  linarith [hrow k]

/-- The matrix is genuinely positive definite over the reals. -/
theorem workedWitness_posDef : workedWitness.PosDef :=
  posDef_of_diagonal_dominance workedWitness_isHermitian
    workedWitness_diagonal workedWitness_row_sum_lt_one

/-- The three canonical full-support premises hold exactly. -/
theorem workedWitness_premises :
    singletonCI workedWitness 0 1 2 ∧
    singletonCI workedWitness 0 2 3 ∧
    singletonCI workedWitness 0 3 4 := by
  norm_num [singletonCI, workedWitness, witness12, witness13, witness14,
    witness15, witness23, witness24, witness25, witness34, witness35, witness45]

/-- Its unconditioned covariance entry is strictly positive. -/
theorem workedWitness_marginal_positive : 0 < workedWitness 0 1 := by
  norm_num [workedWitness, witness12, witness13, witness14, witness15,
    witness23, witness34, witness45]

/-- This positive-definite Gaussian matrix refutes the indicated conclusion. -/
theorem workedWitness_not_marginal : ¬ marginalCI workedWitness 0 1 := by
  exact ne_of_gt workedWitness_marginal_positive

/-- A concrete, unconditional three-premise Gaussian counterexample. -/
theorem exists_worked_gaussian_counterexample :
    ∃ R : Matrix (Fin 5) (Fin 5) ℝ,
      R.PosDef ∧ (∀ i, R i i = 1) ∧
      singletonCI R 0 1 2 ∧ singletonCI R 0 2 3 ∧ singletonCI R 0 3 4 ∧
      ¬ marginalCI R 0 1 := by
  exact ⟨workedWitness, workedWitness_posDef, workedWitness_diagonal,
    workedWitness_premises.1, workedWitness_premises.2.1,
    workedWitness_premises.2.2, workedWitness_not_marginal⟩

#print axioms workedWitness_posDef
#print axioms workedWitness_premises
#print axioms workedWitness_not_marginal
#print axioms exists_worked_gaussian_counterexample

end
end GaussianCI
