module

public import GaussianCI.WorkedWitness

@[expose] public section

/-!
# Premise minimality of the five-variable Gaussian cycle

Rotations of the rim labels `2,3,4,5` turn the exact witness of certificate 272
into a counterexample for each deletion of one cycle premise. Every covariance
between the center and a rim label is nonzero, so the same marginal conclusion
is refuted after reindexing. This argument does not use the exhaustive lower
bound or any unproved certificate-coverage assumption.
-/

namespace GaussianCI

/-- The four singleton CI premises, in their cyclic order. -/
def cyclePremise (R : Matrix (Fin 5) (Fin 5) ℝ) (j : Fin 4) : Prop :=
  ![singletonCI R 0 1 2, singletonCI R 0 2 3,
    singletonCI R 0 3 4, singletonCI R 0 4 1] j

def cycleReindex (deleted : Fin 4) : Fin 5 → Fin 5 :=
  ![![0, 4, 1, 2, 3], ![0, 3, 4, 1, 2],
    ![0, 2, 3, 4, 1], ![0, 1, 2, 3, 4]] deleted

private theorem cycleReindex_injective (deleted : Fin 4) :
    Function.Injective (cycleReindex deleted) := by
  intro i j hij
  fin_cases deleted <;> fin_cases i <;> fin_cases j <;>
    simp_all [cycleReindex]

/-- Reindexing the exact worked witness rotates its missing cycle premise. -/
noncomputable def minimalityWitness (deleted : Fin 4) : Matrix (Fin 5) (Fin 5) ℝ :=
  workedWitness.submatrix (cycleReindex deleted) (cycleReindex deleted)

private theorem workedWitness_star_nonzero (j : Fin 4) :
    workedWitness 0 j.succ ≠ 0 := by
  fin_cases j
  · change ((((-7512862 : ℝ) / 32408079 * (4785782 / 33720645)) *
      (7894693 / 48443657)) * (-5076563 / 95066657)) ≠ 0
    norm_num
  · change (((-7512862 : ℝ) / 32408079 * (4785782 / 33720645)) *
      (7894693 / 48443657)) ≠ 0
    norm_num
  · change ((-7512862 : ℝ) / 32408079 * (4785782 / 33720645)) ≠ 0
    norm_num
  · change (-7512862 : ℝ) / 32408079 ≠ 0
    norm_num

theorem minimalityWitness_posDef (deleted : Fin 4) :
    (minimalityWitness deleted).PosDef :=
  workedWitness_posDef.submatrix (cycleReindex_injective deleted)

theorem minimalityWitness_diagonal (deleted : Fin 4) (i : Fin 5) :
    minimalityWitness deleted i i = 1 :=
  workedWitness_diagonal (cycleReindex deleted i)

/-- Every premise except the selected deletion holds. -/
theorem minimalityWitness_premises (deleted j : Fin 4) (hj : j ≠ deleted) :
    cyclePremise (minimalityWitness deleted) j := by
  have h₀ := workedWitness_premises.1
  have h₁ := workedWitness_premises.2.1
  have h₂ := workedWitness_premises.2.2
  fin_cases deleted <;> fin_cases j <;>
    simp_all [cyclePremise, singletonCI, minimalityWitness, cycleReindex, Matrix.submatrix]

/-- Rotating the witness never makes the fixed marginal conclusion true. -/
theorem minimalityWitness_not_marginal (deleted : Fin 4) :
    ¬ marginalCI (minimalityWitness deleted) 0 1 := by
  fin_cases deleted
  · simpa [marginalCI, minimalityWitness, cycleReindex, Matrix.submatrix] using
      workedWitness_star_nonzero 3
  · simpa [marginalCI, minimalityWitness, cycleReindex, Matrix.submatrix] using
      workedWitness_star_nonzero 2
  · simpa [marginalCI, minimalityWitness, cycleReindex, Matrix.submatrix] using
      workedWitness_star_nonzero 1
  · simpa [marginalCI, minimalityWitness, cycleReindex, Matrix.submatrix] using
      workedWitness_star_nonzero 0

/-- Each single-premise deletion admits a positive-definite Gaussian
counterexample to the cycle's marginal conclusion. -/
theorem cycle_each_deletion_counterexample (deleted : Fin 4) :
    ∃ R : Matrix (Fin 5) (Fin 5) ℝ,
      R.PosDef ∧ (∀ i, R i i = 1) ∧
      (∀ j : Fin 4, j ≠ deleted → cyclePremise R j) ∧ ¬ marginalCI R 0 1 := by
  exact ⟨minimalityWitness deleted, minimalityWitness_posDef deleted,
    minimalityWitness_diagonal deleted, minimalityWitness_premises deleted,
    minimalityWitness_not_marginal deleted⟩

/-- Every proper subfamily of the cycle premises has such a counterexample. -/
theorem cycle_proper_subfamily_counterexample (P : Finset (Fin 4)) (hP : P ≠ Finset.univ) :
    ∃ R : Matrix (Fin 5) (Fin 5) ℝ,
      R.PosDef ∧ (∀ i, R i i = 1) ∧
      (∀ j ∈ P, cyclePremise R j) ∧ ¬ marginalCI R 0 1 := by
  classical
  have hex : ∃ deleted : Fin 4, deleted ∉ P := by
    by_contra h
    push Not at h
    apply hP
    ext j
    simp [h j]
  obtain ⟨deleted, hdeleted⟩ := hex
  obtain ⟨R, hR, hdiag, hpremises, hconclusion⟩ := cycle_each_deletion_counterexample deleted
  refine ⟨R, hR, hdiag, ?_, hconclusion⟩
  intro j hj
  apply hpremises j
  intro heq
  subst j
  exact hdeleted hj

/-- Gaussian validity of the complete premise family. -/
theorem cycle_all_premises_valid {R : Matrix (Fin 5) (Fin 5) ℝ}
    (hR : R.PosDef)
    (hpremises : ∀ j : Fin 4, cyclePremise R j) : marginalCI R 0 1 := by
  apply gaussian_five_cycle_covariance hR
  · simpa [cyclePremise] using hpremises 0
  · simpa [cyclePremise] using hpremises 1
  · simpa [cyclePremise] using hpremises 2
  · simpa [cyclePremise] using hpremises 3

#print axioms minimalityWitness_posDef
#print axioms minimalityWitness_premises
#print axioms minimalityWitness_not_marginal
#print axioms cycle_each_deletion_counterexample
#print axioms cycle_proper_subfamily_counterexample
#print axioms cycle_all_premises_valid

end GaussianCI
