module

public import GaussianCI.WorkedWitness
public import GaussianCI.Finite

@[expose] public section

/-!
# Exact Gaussian realizations of the ten countermodel four-faces

Each matrix below has rational entries, is strictly diagonally dominant, and
has exactly the CI zero pattern of the corresponding face of the explicit
five-variable countermodel. Thus these ten particular faces are Gaussian
realizable without using an externally supplied catalogue or its classification.

The rational matrices were obtained by solving their two or three independent
zero-minor equations, with free parameters chosen among `1/5,1/7,1/11,1/13`.
The construction was deterministic, with no random seed. An exploratory check
used SymPy 1.14.0 to evaluate the exact rational minors and row sums. SymPy is
not part of the acceptance chain and is not required to build this module.
Acceptance consists of exact kernel arithmetic, the determinant identities
below, and the positive-definiteness theorem for strict diagonal dominance.
No numerical search result is used as a hypothesis.
-/

namespace GaussianCI

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A symmetric correlation matrix from its six upper-triangular entries. -/
def fourCorrelation {α : Type*} [One α] (p : Fin 6 → α) : Matrix (Fin 4) (Fin 4) α :=
  ![![1, p 0, p 1, p 2],
    ![p 0, 1, p 3, p 4],
    ![p 1, p 3, 1, p 5],
    ![p 2, p 4, p 5, 1]]

/-- Six exact rational entries for each marginal (`false`) or conditional
(`true`) four-face, in the increasing order of the surviving labels. -/
def faceParameters (omitted : Nat) (conditioned : Bool) : Fin 6 → ℚ :=
  match omitted, conditioned with
  | 1, false => ![5/77, 1/5, 1/55, 1/77, 1/7, 1/11]
  | 1, true => ![1/5, 1/7, 72/2485, 1/143, 1/11, 1/13]
  | 2, false => ![1/4235, 1/55, 1/5, 1/77, 1/7, 1/11]
  | 2, true => ![1/5, 1/7, 0, 0, 1/11, 1/13]
  | 3, false => ![1/5, 1/4235, 1/385, 1/7, 1/77, 1/11]
  | 3, true => ![0, 1/55, 1/5, 1/7, 11/882, 1/11]
  | 4, false => ![1/35, 1/5, 1/385, 1/7, 1/11, 1/13]
  | 4, true => ![1/5, 0, -5/77, 1/7, 0, 1/11]
  | 5, false => ![1/2695, 1/385, 1/5, 1/7, 1/11, 1/77]
  | 5, true => ![1/5, 1/7, 0, 1/11, 1/13, 0]
  | _, _ => ![0, 0, 0, 0, 0, 0]

def faceWitnessQ (omitted : Nat) (conditioned : Bool) : Matrix (Fin 4) (Fin 4) ℚ :=
  fourCorrelation (faceParameters omitted conditioned)

noncomputable def faceWitness (omitted : Nat) (conditioned : Bool) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (faceWitnessQ omitted conditioned i j : ℝ)

/-- The almost-principal determinant, with rows `i :: K` and columns
`j :: K`. For valid elementary atoms the conditioning labels exclude `i,j`.
The order of `K` agrees with the canonical increasing face-label order. -/
noncomputable def fourAlmostPrincipal {α : Type*} [CommRing α]
    (R : Matrix (Fin 4) (Fin 4) α) (i j : Fin 4) (K : List (Fin 4)) : α :=
  (R.submatrix (i :: K).get (j :: K).get).det

/-- Explicit determinant formulas for conditioning sets of size at most two.
Larger sets are unsupported here; the finite acceptance check separately
verifies that no atom supplied to this formula has such a set. -/
def fourMinorFormula {α : Type*} [CommRing α]
    (R : Matrix (Fin 4) (Fin 4) α) (i j : Fin 4) (K : List (Fin 4)) : α :=
  match K with
  | [] => R i j
  | [k] => R i j * R k k - R i k * R k j
  | [k, l] => R i j * (R k k * R l l - R k l * R l k) -
      R i k * (R k j * R l l - R k l * R l j) +
      R i l * (R k j * R l k - R k k * R l j)
  | _ => 0

/-- The explicit polynomial acceptance formula equals the determinant. -/
theorem fourMinorFormula_eq_det {α : Type*} [CommRing α]
    (R : Matrix (Fin 4) (Fin 4) α) (i j : Fin 4) (K : List (Fin 4))
    (hK : K.length ≤ 2) : fourMinorFormula R i j K = fourAlmostPrincipal R i j K := by
  cases K with
  | nil => simp [fourMinorFormula, fourAlmostPrincipal, Matrix.submatrix]
  | cons k K =>
    cases K with
    | nil => simp [fourMinorFormula, fourAlmostPrincipal, Matrix.det_fin_two,
        Matrix.submatrix]
    | cons l K =>
      cases K with
      | nil =>
        simp [fourMinorFormula, fourAlmostPrincipal, Matrix.det_fin_three,
          Matrix.submatrix]
        ring
      | cons m K => simp at hK

theorem fourMinorFormula_cast (R : Matrix (Fin 4) (Fin 4) ℚ)
    (i j : Fin 4) (K : List (Fin 4)) :
    fourMinorFormula (fun a b => (R a b : ℝ)) i j K =
      ((fourMinorFormula R i j K : ℚ) : ℝ) := by
  cases K with
  | nil => simp [fourMinorFormula]
  | cons k K =>
    cases K with
    | nil => simp [fourMinorFormula]
    | cons l K =>
      cases K with
      | nil => simp [fourMinorFormula]
      | cons m K => simp [fourMinorFormula]

/-- Translate an original variable label into its zero-based position in a
four-face. The modulo makes the function total; every accepted atom below is
enumerated on the four surviving labels, so no invalid position is accepted. -/
def faceLocalIndex (omitted label : Nat) : Fin 4 :=
  ⟨(faceVariables omitted).idxOf label % 4, Nat.mod_lt _ (by decide)⟩

def faceLocalConditioning (omitted conditioning : Nat) : List (Fin 4) :=
  (List.finRange 4).filter fun k =>
    conditioning.testBit ((faceVariables omitted).getD k.val 0)

/-- The label encoding represents a proper elementary four-variable atom:
both endpoints decode correctly, are distinct, and are absent from a duplicate-
free conditioning list of length at most two. -/
abbrev WellFormedFaceAtom (omitted : Nat) (atom : FiniteAtom) : Prop :=
  (faceVariables omitted).getD (faceLocalIndex omitted atom.1).val 0 = atom.1 ∧
  (faceVariables omitted).getD (faceLocalIndex omitted atom.2.1).val 0 = atom.2.1 ∧
  faceLocalIndex omitted atom.1 ≠ faceLocalIndex omitted atom.2.1 ∧
  faceLocalIndex omitted atom.1 ∉ faceLocalConditioning omitted atom.2.2 ∧
  faceLocalIndex omitted atom.2.1 ∉ faceLocalConditioning omitted atom.2.2 ∧
  (faceLocalConditioning omitted atom.2.2).Nodup ∧
  (faceLocalConditioning omitted atom.2.2).length ≤ 2

/-- Exact rational acceptance of every one of the 240 face atoms. In addition
to zero/nonzero agreement, the check enforces the domain of the determinant
formula used to evaluate an atom. -/
def faceWitnessChecks : Bool :=
  fourFaces.all fun face =>
    (elementaryAtoms (faceVariables face.1)).all fun atom =>
      decide (WellFormedFaceAtom face.1 atom ∧
        (fourMinorFormula (faceWitnessQ face.1 face.2)
          (faceLocalIndex face.1 atom.1) (faceLocalIndex face.1 atom.2.1)
          (faceLocalConditioning face.1 atom.2.2) = 0 ↔
          faceHas cycleCountermodelHas face.1 face.2 atom.1 atom.2.1 atom.2.2 = true))

theorem faceWitnessChecks_correct : faceWitnessChecks = true := by
  decide +kernel

theorem faceWitness_atom_wellFormed (omitted : Nat) (conditioned : Bool)
    (hface : (omitted, conditioned) ∈ fourFaces) (atom : FiniteAtom)
    (hatom : atom ∈ elementaryAtoms (faceVariables omitted)) :
    WellFormedFaceAtom omitted atom := by
  have hall := List.all_eq_true.mp faceWitnessChecks_correct
  have hlocal := List.all_eq_true.mp (hall (omitted, conditioned) hface) atom hatom
  exact (of_decide_eq_true hlocal).1

theorem faceWitness_diagonal (omitted : Nat) (conditioned : Bool) (i : Fin 4) :
    faceWitness omitted conditioned i i = 1 := by
  fin_cases i <;> simp [faceWitness, faceWitnessQ, fourCorrelation]

theorem faceWitness_isHermitian (omitted : Nat) (conditioned : Bool) :
    (faceWitness omitted conditioned).IsHermitian := by
  ext i j
  change star (faceWitness omitted conditioned j i) = faceWitness omitted conditioned i j
  fin_cases i <;> fin_cases j <;> simp [faceWitness, faceWitnessQ, fourCorrelation]

theorem faceWitness_row_sum_lt_one (omitted : Nat) (conditioned : Bool)
    (hface : (omitted, conditioned) ∈ fourFaces) (i : Fin 4) :
    (∑ j ∈ Finset.univ.erase i, ‖faceWitness omitted conditioned i j‖) < 1 := by
  cases conditioned <;>
    simp [fourFaces, fiveVariables] at hface <;>
    rcases hface with rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;>
    norm_num [-Rat.norm_cast_real, Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Fin.sum_univ_succ, faceWitness, faceWitnessQ, fourCorrelation, faceParameters,
      Real.norm_eq_abs]

/-- Each of the ten rational matrices is positive definite over the reals. -/
theorem faceWitness_posDef (omitted : Nat) (conditioned : Bool)
    (hface : (omitted, conditioned) ∈ fourFaces) :
    (faceWitness omitted conditioned).PosDef :=
  posDef_of_diagonal_dominance (faceWitness_isHermitian omitted conditioned)
    (faceWitness_diagonal omitted conditioned)
    (faceWitness_row_sum_lt_one omitted conditioned hface)

/-- Agreement of each real almost-principal determinant with the complete face
CI structure, including all absent atoms. -/
theorem faceWitness_exact_pattern (omitted : Nat) (conditioned : Bool)
    (hface : (omitted, conditioned) ∈ fourFaces) (atom : FiniteAtom)
    (hatom : atom ∈ elementaryAtoms (faceVariables omitted)) :
    (fourAlmostPrincipal (faceWitness omitted conditioned)
      (faceLocalIndex omitted atom.1) (faceLocalIndex omitted atom.2.1)
      (faceLocalConditioning omitted atom.2.2) = 0 ↔
      faceHas cycleCountermodelHas omitted conditioned atom.1 atom.2.1 atom.2.2 = true) := by
  have hall := List.all_eq_true.mp faceWitnessChecks_correct
  have hlocal := List.all_eq_true.mp (hall (omitted, conditioned) hface) atom hatom
  obtain ⟨hdomain, hpattern⟩ := of_decide_eq_true hlocal
  obtain ⟨_, _, _, _, _, _, hsize⟩ := hdomain
  rw [← fourMinorFormula_eq_det _ _ _ _ hsize]
  unfold faceWitness
  rw [fourMinorFormula_cast]
  simpa only [Rat.cast_eq_zero] using hpattern

/-- Every marginal and conditional four-face of the explicit countermodel is
realized by a positive-definite real Gaussian covariance matrix, with exact
agreement on all elementary atoms. This avoids the four-variable catalogue
classification for the nonlocality argument. -/
theorem cycleCountermodel_faces_gaussian_realizable
    (omitted : Nat) (conditioned : Bool) (hface : (omitted, conditioned) ∈ fourFaces) :
    ∃ R : Matrix (Fin 4) (Fin 4) ℝ,
      R.PosDef ∧ (∀ i, R i i = 1) ∧
      ∀ atom ∈ elementaryAtoms (faceVariables omitted),
        (fourAlmostPrincipal R
          (faceLocalIndex omitted atom.1) (faceLocalIndex omitted atom.2.1)
          (faceLocalConditioning omitted atom.2.2) = 0 ↔
          faceHas cycleCountermodelHas omitted conditioned atom.1 atom.2.1 atom.2.2 = true) := by
  exact ⟨faceWitness omitted conditioned, faceWitness_posDef omitted conditioned hface,
    faceWitness_diagonal omitted conditioned,
    faceWitness_exact_pattern omitted conditioned hface⟩

/-- Semantic Gaussian realizability of one four-face: a positive-definite real
covariance matrix has exactly its 24 elementary almost-principal zero minors. -/
def FourFaceRealizable (has : Nat → Nat → ConditioningMask → Bool)
    (omitted : Nat) (conditioned : Bool) : Prop :=
  ∃ R : Matrix (Fin 4) (Fin 4) ℝ, R.PosDef ∧
    ∀ atom ∈ elementaryAtoms (faceVariables omitted),
      (fourAlmostPrincipal R
        (faceLocalIndex omitted atom.1) (faceLocalIndex omitted atom.2.1)
        (faceLocalConditioning omitted atom.2.2) = 0 ↔
        faceHas has omitted conditioned atom.1 atom.2.1 atom.2.2 = true)

/-- A semantic model of all ten marginal and conditional Gaussian four-faces.
This definition does not mention a supplied finite catalogue. -/
def FourLocalModel (has : Nat → Nat → ConditioningMask → Bool) : Prop :=
  ∀ omitted conditioned, (omitted, conditioned) ∈ fourFaces →
    FourFaceRealizable has omitted conditioned

theorem cycleCountermodel_four_local : FourLocalModel cycleCountermodelHas := by
  intro omitted conditioned hface
  obtain ⟨R, hR, _, hpattern⟩ :=
    cycleCountermodel_faces_gaussian_realizable omitted conditioned hface
  exact ⟨R, hR, hpattern⟩

/-- The five-variable four-premise cycle rule, evaluated on an abstract CI
structure in the original manuscript's label convention. -/
def CycleRuleHolds (has : Nat → Nat → ConditioningMask → Bool) : Prop :=
  (has 1 2 (2 ^ 3) = true ∧ has 1 3 (2 ^ 4) = true ∧
    has 1 4 (2 ^ 5) = true ∧ has 1 5 (2 ^ 2) = true) → has 1 2 0 = true

/-- The Gaussian-valid cycle implication is not a semantic consequence of
requiring all ten four-faces to be Gaussian realizable. Ten explicit covariance
witnesses establish the countermodel's face realizability without using the
629-row classification. -/
theorem cycle_rule_not_four_local :
    ¬ ∀ has : Nat → Nat → ConditioningMask → Bool, FourLocalModel has → CycleRuleHolds has := by
  intro hlocal
  have hcycle := hlocal cycleCountermodelHas cycleCountermodel_four_local
  obtain ⟨h₁, h₂, h₃, h₄, hfailed⟩ := cycleCountermodel_premises_and_failed_conclusion
  have hconclusion := hcycle ⟨h₁, h₂, h₃, h₄⟩
  rw [hfailed] at hconclusion
  contradiction

#print axioms fourMinorFormula_eq_det
#print axioms faceWitnessChecks_correct
#print axioms faceWitness_atom_wellFormed
#print axioms faceWitness_posDef
#print axioms faceWitness_exact_pattern
#print axioms cycleCountermodel_faces_gaussian_realizable
#print axioms cycleCountermodel_four_local
#print axioms cycle_rule_not_four_local

end GaussianCI
