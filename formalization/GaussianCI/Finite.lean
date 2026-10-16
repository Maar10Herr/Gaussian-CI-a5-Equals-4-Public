module

public import Mathlib.Data.List.Basic

/-!
# Direct finite checks for the five-variable countermodel

The definitions below mirror the mathematical elementary gaussoid axioms and
the five Lněnička–Matúš implication schemes. The countermodel is an explicit
membership mask, with the first elementary atom stored in its least significant
bit. Its atom order is the order used by `independent/catalogue.py`.

Every theorem in this module is checked by Lean's kernel. No external catalogue,
Python return value, `native_decide`, or extra axiom is used to accept the
countermodel. This module does not formalize the Gaussian-realizability
classification or the lower bound in the paper.
-/

@[expose] public section

namespace GaussianCI

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A conditioning set is represented by a bit mask: variable `i` uses bit `i`.
Variables have labels `1, …, 5`; bit zero is unused. -/
abbrev ConditioningMask := Nat

/-- An elementary CI atom consists of its ordered pair and conditioning mask. -/
abbrev FiniteAtom := Nat × Nat × ConditioningMask

/-- All subsets, in increasing binary order on the supplied variable list. -/
def conditioningSubsets (labels : List Nat) : List ConditioningMask :=
  labels.foldl (fun subsets i => subsets ++ subsets.map (· + 2 ^ i)) [0]

/-- All elementary atoms on a list of distinct labels. -/
def elementaryAtoms (labels : List Nat) : List FiniteAtom :=
  labels.flatMap fun i =>
    (labels.filter (i < ·)).flatMap fun j =>
      (conditioningSubsets (labels.filter fun k => k != i && k != j)).map
        fun conditioning => (i, j, conditioning)

def fiveVariables : List Nat := [1, 2, 3, 4, 5]
def fiveAtoms : List FiniteAtom := elementaryAtoms fiveVariables

/-- Lookup in the explicit elementary atom order. Invalid atoms are absent. -/
def maskHasOn (labels : List Nat) (mask : Nat) (i j : Nat)
    (conditioning : ConditioningMask) : Bool :=
  let atoms := elementaryAtoms labels
  let index := atoms.idxOf (min i j, max i j, conditioning)
  index < atoms.length && mask.testBit index

def maskHas := maskHasOn fiveVariables

/-- Membership bits from `certificates/cycle_rule_t4_countermodel.txt`.
Present zero-based atom positions are `1,10,20,22,25,52,55,58,60,61`. -/
def cycleCountermodelMask : Nat := 3787527286657385474

def cycleCountermodelHas := maskHas cycleCountermodelMask

theorem cycleCountermodel_mask_bounded : cycleCountermodelMask < 2 ^ 80 := by
  decide +kernel

theorem cycleCountermodel_present_indices :
    (List.range 80).filter cycleCountermodelMask.testBit =
      [1, 10, 20, 22, 25, 52, 55, 58, 60, 61] := by decide +kernel

def orderedTriples (labels : List Nat) : List (Nat × Nat × Nat) :=
  labels.flatMap fun i =>
    (labels.filter (· != i)).flatMap fun j =>
      (labels.filter fun k => k != i && k != j).map fun k => (i, j, k)

def orderedQuadruples (labels : List Nat) : List (Nat × Nat × Nat × Nat) :=
  labels.flatMap fun i =>
    (labels.filter (· != i)).flatMap fun j =>
      (labels.filter fun k => k != i && k != j).flatMap fun k =>
        (labels.filter fun l => l != i && l != j && l != k).map fun l =>
          (i, j, k, l)

/-- Conjunction of the four elementary gaussoid axioms at `i,j,k,L`.
The fourth axiom has a disjunctive conclusion. -/
def elementaryGaussoidAxioms
    (has : Nat → Nat → ConditioningMask → Bool)
    (i j k : Nat) (conditioning : ConditioningMask) : Bool :=
  let ij := has i j conditioning
  let ik := has i k conditioning
  let jk := has j k conditioning
  let ikj := has i k (conditioning + 2 ^ j)
  let ijk := has i j (conditioning + 2 ^ k)
  (!(ij && ikj) || (ik && ijk)) &&
    (!(ijk && ikj) || (ij && ik)) &&
    (!(ij && ik) || (ijk && ikj)) &&
    (!(ij && ijk) || (ik || jk))

theorem bool_implication_iff (premise conclusion : Bool) :
    (!premise || conclusion) = true ↔ (premise = true → conclusion = true) := by
  cases premise <;> cases conclusion <;> decide

/-- The Boolean checker has exactly the usual implication semantics. -/
theorem elementaryGaussoidAxioms_iff
    (has : Nat → Nat → ConditioningMask → Bool)
    (i j k : Nat) (conditioning : ConditioningMask) :
    elementaryGaussoidAxioms has i j k conditioning = true ↔
      ((has i j conditioning = true ∧ has i k (conditioning + 2 ^ j) = true) →
        (has i k conditioning = true ∧ has i j (conditioning + 2 ^ k) = true)) ∧
      ((has i j (conditioning + 2 ^ k) = true ∧
          has i k (conditioning + 2 ^ j) = true) →
        (has i j conditioning = true ∧ has i k conditioning = true)) ∧
      ((has i j conditioning = true ∧ has i k conditioning = true) →
        (has i j (conditioning + 2 ^ k) = true ∧
          has i k (conditioning + 2 ^ j) = true)) ∧
      ((has i j conditioning = true ∧ has i j (conditioning + 2 ^ k) = true) →
        (has i k conditioning = true ∨ has j k conditioning = true)) := by
  simp only [elementaryGaussoidAxioms, Bool.and_eq_true_iff]
  simp only [bool_implication_iff]
  simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff, and_assoc]

def gaussoidCheck (labels : List Nat)
    (has : Nat → Nat → ConditioningMask → Bool) : Bool :=
  (orderedTriples labels).all fun (i, j, k) =>
    (conditioningSubsets
      (labels.filter fun l => l != i && l != j && l != k)).all fun conditioning =>
        elementaryGaussoidAxioms has i j k conditioning

/-- Conjunction of all five Lněnička–Matúš higher implication schemes.
Relabelling is handled by checking all ordered distinct quadruples. -/
def lmHigherSchemes
    (has : Nat → Nat → ConditioningMask → Bool) (i j k l : Nat) : Bool :=
  (!(has i j 0 && has k l 0 && has i k (2 ^ j + 2 ^ l) &&
      has j l (2 ^ i + 2 ^ k)) || has i k 0) &&
    (!(has i j 0 && has k l (2 ^ i) && has k l (2 ^ j) &&
      has i j (2 ^ k + 2 ^ l)) || has k l 0) &&
    (!(has i j 0 && has j l (2 ^ k) && has k l (2 ^ i) &&
      has i k (2 ^ j + 2 ^ l)) || has i k 0) &&
    (!(has i j (2 ^ k) && has i k (2 ^ l) && has i l (2 ^ j)) || has i j 0) &&
    (!(has i j (2 ^ k) && has i k (2 ^ l) && has j l (2 ^ i) &&
      has k l (2 ^ j)) || has i j 0)

def lmHigherCheck (labels : List Nat)
    (has : Nat → Nat → ConditioningMask → Bool) : Bool :=
  (orderedQuadruples labels).all fun (i, j, k, l) => lmHigherSchemes has i j k l

/-- The two four-variable faces for each omitted variable: marginal and
conditional. `false` means marginal; `true` fixes the omitted variable in every
conditioning set. -/
def fourFaces : List (Nat × Bool) :=
  fiveVariables.flatMap fun omitted => [(omitted, false), (omitted, true)]

def faceVariables (omitted : Nat) : List Nat := fiveVariables.filter (· != omitted)

def faceHas (has : Nat → Nat → ConditioningMask → Bool)
    (omitted : Nat) (conditioned : Bool)
    (i j : Nat) (conditioning : ConditioningMask) : Bool :=
  has i j (conditioning + if conditioned then 2 ^ omitted else 0)

def faceAxiomCheck (has : Nat → Nat → ConditioningMask → Bool) : Bool :=
  fourFaces.all fun (omitted, conditioned) =>
    let labels := faceVariables omitted
    let localHas := faceHas has omitted conditioned
    gaussoidCheck labels localHas && lmHigherCheck labels localHas

theorem fiveAtoms_length : fiveAtoms.length = 80 := by decide +kernel

theorem fiveAtoms_distinct : fiveAtoms.Nodup := by decide +kernel

theorem fourFaces_length : fourFaces.length = 10 := by decide +kernel

theorem fourFaces_atom_lengths :
    fourFaces.all (fun face => (elementaryAtoms (faceVariables face.1)).length == 24) =
      true := by decide +kernel

theorem cycleCountermodel_premises_and_failed_conclusion :
    cycleCountermodelHas 1 2 (2 ^ 3) = true ∧
    cycleCountermodelHas 1 3 (2 ^ 4) = true ∧
    cycleCountermodelHas 1 4 (2 ^ 5) = true ∧
    cycleCountermodelHas 1 5 (2 ^ 2) = true ∧
    cycleCountermodelHas 1 2 0 = false := by decide +kernel

/-- All four elementary gaussoid axioms hold for every ordered distinct triple
and every disjoint conditioning set on five labels. -/
theorem cycleCountermodel_gaussoid :
    gaussoidCheck fiveVariables cycleCountermodelHas = true := by decide +kernel

/-- Each of the ten faces directly satisfies the elementary gaussoid axioms
and every relabelling of each of the five higher schemes. -/
theorem cycleCountermodel_ten_faces_axioms :
    faceAxiomCheck cycleCountermodelHas = true := by decide +kernel

/-- The global checker entails each individual instance of the four axioms. -/
theorem cycleCountermodel_gaussoid_instance (i j k conditioning : Nat)
    (htriple : (i, j, k) ∈ orderedTriples fiveVariables)
    (hconditioning : conditioning ∈ conditioningSubsets
      (fiveVariables.filter fun l => l != i && l != j && l != k)) :
    elementaryGaussoidAxioms cycleCountermodelHas i j k conditioning = true := by
  exact List.all_eq_true.mp
    (List.all_eq_true.mp cycleCountermodel_gaussoid (i, j, k) htriple)
      conditioning hconditioning

/-- The face checker entails each individual higher-scheme instance. -/
theorem cycleCountermodel_face_higher_instance
    (omitted : Nat) (conditioned : Bool) (i j k l : Nat)
    (hface : (omitted, conditioned) ∈ fourFaces)
    (hquadruple : (i, j, k, l) ∈ orderedQuadruples (faceVariables omitted)) :
    lmHigherSchemes (faceHas cycleCountermodelHas omitted conditioned) i j k l =
      true := by
  have hchecks := List.all_eq_true.mp cycleCountermodel_ten_faces_axioms
    (omitted, conditioned) hface
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hchecks).2
    (i, j, k, l) hquadruple

/-- Relabelling, optionally followed by CI duality. Duality complements the
conditioning set inside the three variables outside the atom's pair. -/
def symmetryAtomImage (permutation : List Nat) (dual : Bool)
    (atom : FiniteAtom) : FiniteAtom :=
  let image i := permutation.getD (i - 1) 0
  let conditioning :=
    (fiveVariables.filter fun k => k != atom.1 && k != atom.2.1).foldl
      (fun mask k =>
        if atom.2.2.testBit k != dual then mask + 2 ^ image k else mask) 0
  (min (image atom.1) (image atom.2.1),
    max (image atom.1) (image atom.2.1), conditioning)

/-- The atom maps generated by all `5!` relabellings and the two duality choices.
An entry is the image atom's zero-based index. -/
def fiveSymmetryMaps : List (List Nat) :=
  fiveVariables.permutations'.flatMap fun permutation =>
    [false, true].map fun dual =>
      fiveAtoms.map fun atom => fiveAtoms.idxOf (symmetryAtomImage permutation dual atom)

theorem fiveSymmetryMaps_length : fiveSymmetryMaps.length = 240 := by decide +kernel

#print axioms fiveAtoms_length
#print axioms fiveAtoms_distinct
#print axioms cycleCountermodel_premises_and_failed_conclusion
#print axioms cycleCountermodel_gaussoid
#print axioms cycleCountermodel_ten_faces_axioms

end GaussianCI
