module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Bounds.Defs

import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.RCases

@[expose] public section

/-!
# Threshold consequences of checked witness coverage

These theorems take validation of the Gaussian certificate file, closure
computation, four-variable catalogue, and symmetry reduction as hypotheses.
Models are sets of atoms; the intended Gaussian model family must ultimately be
constructed from positive-definite real covariance matrices.
-/

namespace GaussianCI

variable {Atom : Type*}

/-- A model satisfies every atom in a finite premise set. -/
def Satisfies (model : Set Atom) (premises : Finset Atom) : Prop :=
  ∀ atom ∈ premises, atom ∈ model

/-- Semantic validity in a specified family of atom sets. -/
def ValidIn (models : Set (Set Atom)) (premises : Finset Atom) (conclusion : Atom) : Prop :=
  ∀ model ∈ models, Satisfies model premises → conclusion ∈ model

/-- A model satisfying the premises and omitting the conclusion. -/
def HasCounterexample (models : Set (Set Atom)) (premises : Finset Atom)
    (conclusion : Atom) : Prop :=
  ∃ model ∈ models, Satisfies model premises ∧ conclusion ∉ model

/-- All covered conclusions fail simultaneously in one model. -/
def JointCounterexample (models : Set (Set Atom)) (premises covers : Finset Atom) : Prop :=
  ∃ model ∈ models, Satisfies model premises ∧ ∀ conclusion ∈ covers, conclusion ∉ model

theorem satisfies_mono {model : Set Atom} {small large : Finset Atom}
    (hsub : small ⊆ large) (h : Satisfies model large) : Satisfies model small := by
  intro atom hatom
  exact h atom (hsub hatom)

theorem validIn_mono_premises {models : Set (Set Atom)} {small large : Finset Atom}
    {conclusion : Atom} (hsub : small ⊆ large)
    (hvalid : ValidIn models small conclusion) : ValidIn models large conclusion := by
  intro model hmodel hpremises
  exact hvalid model hmodel (satisfies_mono hsub hpremises)

theorem validIn_of_models_subset {small large : Set (Set Atom)}
    {premises : Finset Atom} {conclusion : Atom} (hsub : small ⊆ large)
    (hvalid : ValidIn large premises conclusion) : ValidIn small premises conclusion := by
  intro model hmodel hpremises
  exact hvalid model (hsub hmodel) hpremises

theorem not_validIn_of_counterexample {models : Set (Set Atom)}
    {premises : Finset Atom} {conclusion : Atom}
    (hcounter : HasCounterexample models premises conclusion) :
    ¬ ValidIn models premises conclusion := by
  rintro hvalid
  rcases hcounter with ⟨model, hmodel, hpremises, hconclusion⟩
  exact hconclusion (hvalid model hmodel hpremises)

theorem counterexample_mono_premises {models : Set (Set Atom)}
    {small large : Finset Atom} {conclusion : Atom} (hsub : small ⊆ large)
    (hcounter : HasCounterexample models large conclusion) :
    HasCounterexample models small conclusion := by
  rcases hcounter with ⟨model, hmodel, hpremises, hconclusion⟩
  exact ⟨model, hmodel, satisfies_mono hsub hpremises, hconclusion⟩

/-- Soundness required of a closure computation. -/
def ClosureSound (models : Set (Set Atom)) (closure : Finset Atom → Finset Atom) : Prop :=
  ∀ premises conclusion, conclusion ∈ closure premises → ValidIn models premises conclusion

/-- Finite iteration of a closure step, with no assumed termination bound. -/
def iterateClosure (step : Finset Atom → Finset Atom) (premises : Finset Atom) :
    ℕ → Finset Atom
  | 0 => premises
  | n + 1 => step (iterateClosure step premises n)

/-- A sound local inference step stays sound after any finite number of passes. -/
theorem iterateClosure_sound {models : Set (Set Atom)} {step : Finset Atom → Finset Atom}
    (hstep : ClosureSound models step) (n : ℕ) :
    ClosureSound models (fun premises => iterateClosure step premises n) := by
  induction n with
  | zero =>
      intro premises conclusion hconclusion model _ hpremises
      exact hpremises conclusion hconclusion
  | succ n ih =>
      intro premises conclusion hconclusion model hmodel hpremises
      apply hstep (iterateClosure step premises n) conclusion hconclusion model hmodel
      intro atom hatom
      exact ih premises atom hatom model hmodel hpremises

/-- The finite certificate covers give counterexamples to every omitted atom. -/
theorem counterexample_of_certificate_cover {Certificate : Type*}
    {models : Set (Set Atom)} {premises forced : Finset Atom}
    {certificates : Finset Certificate} {covers : Certificate → Finset Atom}
    (hcertificate : ∀ certificate ∈ certificates,
      JointCounterexample models premises (covers certificate))
    (hcoverage : ∀ conclusion ∉ forced,
      ∃ certificate ∈ certificates, conclusion ∈ covers certificate)
    {conclusion : Atom} (houtside : conclusion ∉ forced) :
    HasCounterexample models premises conclusion := by
  rcases hcoverage conclusion houtside with ⟨certificate, hcertificate_mem, hcovered⟩
  rcases hcertificate certificate hcertificate_mem with
    ⟨model, hmodel, hpremises, hfalse⟩
  exact ⟨model, hmodel, hpremises, hfalse conclusion hcovered⟩

/-- The repository's coverage equality implies the per-conclusion coverage condition. -/
theorem counterexample_of_exact_cover [Fintype Atom] [DecidableEq Atom]
    {Certificate : Type*} {models : Set (Set Atom)} {premises forced : Finset Atom}
    {certificates : Finset Certificate} {covers : Certificate → Finset Atom}
    (hcertificate : ∀ certificate ∈ certificates,
      JointCounterexample models premises (covers certificate))
    (hcoverage : certificates.biUnion covers = Finset.univ \ forced)
    {conclusion : Atom} (houtside : conclusion ∉ forced) :
    HasCounterexample models premises conclusion := by
  classical
  apply counterexample_of_certificate_cover hcertificate _ houtside
  intro atom hatom
  have hmem : atom ∈ certificates.biUnion covers := by
    rw [hcoverage]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hatom
  exact Finset.mem_biUnion.mp hmem

/-- Exhaustive witness coverage forces each valid conclusion into the computed closure. -/
theorem valid_forces_closure_of_counterexamples
    {gaussianModels : Set (Set Atom)} {closure : Finset Atom → Finset Atom}
    {premises : Finset Atom} {conclusion : Atom}
    (hcoverage : ∀ atom ∉ closure premises,
      HasCounterexample gaussianModels premises atom)
    (hvalid : ValidIn gaussianModels premises conclusion) :
    conclusion ∈ closure premises := by
  classical
  by_contra houtside
  exact not_validIn_of_counterexample (hcoverage conclusion houtside) hvalid

/-- Sound closure and exhaustive counterexamples imply local validity. -/
theorem valid_implies_local_of_sound_closure_and_coverage
    {gaussianModels localModels : Set (Set Atom)}
    {closure : Finset Atom → Finset Atom} {premises : Finset Atom} {conclusion : Atom}
    (hsound : ClosureSound localModels closure)
    (hcoverage : ∀ atom ∉ closure premises,
      HasCounterexample gaussianModels premises atom)
    (hvalid : ValidIn gaussianModels premises conclusion) :
    ValidIn localModels premises conclusion :=
  hsound premises conclusion (valid_forces_closure_of_counterexamples hcoverage hvalid)

/-- If Gaussian structures satisfy the local theory, the closure is exact on this premise set. -/
theorem valid_iff_closure_mem_of_sound_closure_and_coverage
    {gaussianModels localModels : Set (Set Atom)}
    {closure : Finset Atom → Finset Atom} {premises : Finset Atom} {conclusion : Atom}
    (hmodels : gaussianModels ⊆ localModels)
    (hsound : ClosureSound localModels closure)
    (hcoverage : ∀ atom ∉ closure premises,
      HasCounterexample gaussianModels premises atom) :
    ValidIn gaussianModels premises conclusion ↔ conclusion ∈ closure premises := by
  constructor
  · exact valid_forces_closure_of_counterexamples hcoverage
  · intro hmem
    exact validIn_of_models_subset hmodels (hsound premises conclusion hmem)

/-- Padding needs an independently checked extension relation; it is not automatic. -/
theorem counterexamples_of_finite_padding
    {models : Set (Set Atom)} {closure : Finset Atom → Finset Atom}
    {eligible : Finset Atom → Prop} {premises : Finset Atom}
    (hpadding : ∀ conclusion ∉ closure premises,
      ∃ extended, premises ⊆ extended ∧ eligible extended ∧ conclusion ∉ closure extended)
    (heligible : ∀ extended, eligible extended → ∀ conclusion ∉ closure extended,
      HasCounterexample models extended conclusion) :
    ∀ conclusion ∉ closure premises, HasCounterexample models premises conclusion := by
  intro conclusion houtside
  rcases hpadding conclusion houtside with ⟨extended, hsub, hextended, hnotforced⟩
  exact counterexample_mono_premises hsub
    (heligible extended hextended conclusion hnotforced)

/-- The specific finite-padding route from three antecedents to smaller premise sets. -/
theorem counterexamples_of_three_premise_padding
    {models : Set (Set Atom)} {closure : Finset Atom → Finset Atom}
    {premises : Finset Atom}
    (hpadding : ∀ conclusion ∉ closure premises,
      ∃ extended, premises ⊆ extended ∧ extended.card = 3 ∧ conclusion ∉ closure extended)
    (hthree : ∀ extended, extended.card = 3 → ∀ conclusion ∉ closure extended,
      HasCounterexample models extended conclusion) :
    ∀ conclusion ∉ closure premises, HasCounterexample models premises conclusion :=
  counterexamples_of_finite_padding hpadding hthree

/-- Minimality concerns Gaussian validity, including every proper premise subset. -/
def PremiseMinimal (models : Set (Set Atom)) (premises : Finset Atom)
    (conclusion : Atom) : Prop :=
  ValidIn models premises conclusion ∧
    ∀ smaller, smaller ⊂ premises → ¬ ValidIn models smaller conclusion

/-- Nonlocality of a rule persists after deleting premises. -/
theorem nonlocal_of_subset {localModels : Set (Set Atom)}
    {premises smaller : Finset Atom} {conclusion : Atom}
    (hnonlocal : ¬ ValidIn localModels premises conclusion) (hsub : smaller ⊆ premises) :
    ¬ ValidIn localModels smaller conclusion := by
  intro hvalid
  exact hnonlocal (validIn_mono_premises hsub hvalid)

/-- Locality of every valid deletion establishes minimality of a valid nonlocal rule. -/
theorem premise_minimal_of_local_proper_subsets
    {gaussianModels localModels : Set (Set Atom)}
    {premises : Finset Atom} {conclusion : Atom}
    (hvalid : ValidIn gaussianModels premises conclusion)
    (hnonlocal : ¬ ValidIn localModels premises conclusion)
    (hlower : ∀ smaller, smaller ⊂ premises →
      ValidIn gaussianModels smaller conclusion → ValidIn localModels smaller conclusion) :
    PremiseMinimal gaussianModels premises conclusion := by
  refine ⟨hvalid, ?_⟩
  intro smaller hproper hsmaller
  exact nonlocal_of_subset hnonlocal (Finset.ssubset_iff_subset_ne.mp hproper).1
    (hlower smaller hproper hsmaller)

/-- Four premises and the three-premise lower bound establish premise minimality. -/
theorem premise_minimal_four_of_lower_bound
    {gaussianModels localModels : Set (Set Atom)}
    {premises : Finset Atom} {conclusion : Atom}
    (hcard : premises.card = 4)
    (hvalid : ValidIn gaussianModels premises conclusion)
    (hnonlocal : ¬ ValidIn localModels premises conclusion)
    (hlower : ∀ smaller conclusion, smaller.card ≤ 3 →
      ValidIn gaussianModels smaller conclusion → ValidIn localModels smaller conclusion) :
    PremiseMinimal gaussianModels premises conclusion := by
  apply premise_minimal_of_local_proper_subsets hvalid hnonlocal
  intro smaller hproper hsmaller
  have hlt := Finset.card_lt_card hproper
  have hbound : smaller.card ≤ 3 := by omega
  exact hlower smaller conclusion hbound hsmaller

/-- Conditions for a valid full-support rule outside the local model family. -/
def GenuineBeyond (gaussianModels localModels : Set (Set Atom))
    (fullSupport : Finset Atom → Atom → Prop) (premises : Finset Atom)
    (conclusion : Atom) : Prop :=
  ValidIn gaussianModels premises conclusion ∧ fullSupport premises conclusion ∧
    ¬ ValidIn localModels premises conclusion

/-- Conditional threshold theorem with Gaussian data supplied through hypotheses. -/
theorem threshold_four_of_upper_and_lower
    {gaussianModels localModels : Set (Set Atom)}
    {fullSupport : Finset Atom → Atom → Prop}
    (hupper : ∃ premises conclusion, premises.card = 4 ∧
      GenuineBeyond gaussianModels localModels fullSupport premises conclusion)
    (hlower : ∀ premises conclusion, premises.card ≤ 3 →
      ValidIn gaussianModels premises conclusion → ValidIn localModels premises conclusion) :
    IsLeast {n : ℕ | ∃ premises conclusion, premises.card = n ∧
      GenuineBeyond gaussianModels localModels fullSupport premises conclusion ∧
      PremiseMinimal gaussianModels premises conclusion} 4 := by
  constructor
  · rcases hupper with ⟨premises, conclusion, hcard, hvalid, hsupport, hnonlocal⟩
    exact ⟨premises, conclusion, hcard, ⟨hvalid, hsupport, hnonlocal⟩,
      premise_minimal_four_of_lower_bound hcard hvalid hnonlocal hlower⟩
  · intro n hn
    rcases hn with ⟨premises, conclusion, hcard, hgenuine, _⟩
    by_contra hsmall
    have hbound : premises.card ≤ 3 := by omega
    exact hgenuine.2.2 (hlower premises conclusion hbound hgenuine.1)

#print axioms iterateClosure_sound
#print axioms counterexample_of_exact_cover
#print axioms valid_implies_local_of_sound_closure_and_coverage
#print axioms counterexamples_of_three_premise_padding
#print axioms premise_minimal_four_of_lower_bound
#print axioms threshold_four_of_upper_and_lower

end GaussianCI
