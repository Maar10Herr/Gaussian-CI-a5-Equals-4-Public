module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Rational intervals and their real interpretation

This module proves the real soundness of the exact rational operations used in
the Gaussian-CI certificate verifier. Endpoints need not be ordered: the
enclosure relation itself supplies the order whenever an interval contains a
real value. No rounding model or floating-point assumption is involved.

The expression theorem below covers every polynomial formed from rational
constants, variables, addition, negation, subtraction, and multiplication.
It does not establish the Krawczyk fixed-point theorem or the soundness of the
complete certificate checker.
-/

namespace GaussianCI

/-- Closed rational endpoints, interpreted over the reals by `Encloses`. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval

/-- A real value belongs to the closed interval with these rational endpoints. -/
def Encloses (a : RationalInterval) (x : ℝ) : Prop :=
  (a.lower : ℝ) ≤ x ∧ x ≤ (a.upper : ℝ)

def point (q : ℚ) : RationalInterval := ⟨q, q⟩

def neg (a : RationalInterval) : RationalInterval := ⟨-a.upper, -a.lower⟩

def add (a b : RationalInterval) : RationalInterval :=
  ⟨a.lower + b.lower, a.upper + b.upper⟩

def sub (a b : RationalInterval) : RationalInterval := add a (neg b)

/-- The minimum and maximum of all four endpoint products. -/
def mul (a b : RationalInterval) : RationalInterval :=
  ⟨min (min (a.lower * b.lower) (a.lower * b.upper))
       (min (a.upper * b.lower) (a.upper * b.upper)),
   max (max (a.lower * b.lower) (a.lower * b.upper))
       (max (a.upper * b.lower) (a.upper * b.upper))⟩

theorem point_encloses (q : ℚ) : (point q).Encloses (q : ℝ) :=
  ⟨le_rfl, le_rfl⟩

theorem neg_encloses {a : RationalInterval} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa [Encloses, neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem add_encloses {a b : RationalInterval} {x y : ℝ}
    (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  simpa [Encloses, add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_encloses {a b : RationalInterval} {x y : ℝ}
    (hx : a.Encloses x) (hy : b.Encloses y) :
    (sub a b).Encloses (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_encloses hx (neg_encloses hy)

private theorem linear_mul_bounds {a b x z : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    min (a * z) (b * z) ≤ x * z ∧ x * z ≤ max (a * z) (b * z) := by
  rcases le_total 0 z with hz | hz
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hz),
      (mul_le_mul_of_nonneg_right hx.2 hz).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hz),
      (mul_le_mul_of_nonpos_right hx.1 hz).trans (le_max_left _ _)⟩

private theorem real_mul_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have ha := linear_mul_bounds (z := a) hy
  have hb := linear_mul_bounds (z := b) hy
  simp only [mul_comm] at ha hb
  have hxy := linear_mul_bounds (z := y) hx
  constructor
  · exact (le_min
      ((min_le_left _ _).trans ha.1)
      ((min_le_right _ _).trans hb.1)).trans hxy.1
  · exact hxy.2.trans (max_le
      (ha.2.trans (le_max_left _ _))
      (hb.2.trans (le_max_right _ _)))

theorem mul_encloses {a b : RationalInterval} {x y : ℝ}
    (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  simpa [Encloses, mul, Rat.cast_min, Rat.cast_max] using real_mul_bounds hx hy

/-- A positive lower endpoint proves positivity for every enclosed real value. -/
theorem positive_of_lower {a : RationalInterval} {x : ℝ}
    (hx : a.Encloses x) (ha : 0 < a.lower) : 0 < x := by
  exact (Rat.cast_pos.mpr ha).trans_le hx.1

/-- Excluding zero from a rational interval excludes it from every enclosed value. -/
theorem nonzero_of_excludes_zero {a : RationalInterval} {x : ℝ}
    (hx : a.Encloses x) (ha : a.upper < 0 ∨ 0 < a.lower) : x ≠ 0 := by
  rcases ha with ha | ha
  · have h : x < 0 := hx.2.trans_lt (Rat.cast_lt_zero.mpr ha)
    exact ne_of_lt h
  · exact ne_of_gt (positive_of_lower hx ha)

/-- Sum intervals in the supplied list order, beginning with the point zero. -/
def sum {ι : Type} (indices : List ι) (boxes : ι → RationalInterval) :
    RationalInterval :=
  indices.foldr (fun i total => add (boxes i) total) (point 0)

/-- Multiply intervals in the supplied list order, beginning with the point one. -/
def product {ι : Type} (indices : List ι) (boxes : ι → RationalInterval) :
    RationalInterval :=
  indices.foldr (fun i total => mul (boxes i) total) (point 1)

theorem sum_encloses {ι : Type} (indices : List ι) (boxes : ι → RationalInterval)
    (values : ι → ℝ) (h : ∀ i, (boxes i).Encloses (values i)) :
    (sum indices boxes).Encloses (indices.map values).sum := by
  induction indices with
  | nil => simpa [sum] using point_encloses 0
  | cons i rest ih =>
    simpa only [sum, List.foldr_cons, List.map_cons, List.sum_cons] using
      add_encloses (h i) ih

theorem product_encloses {ι : Type} (indices : List ι) (boxes : ι → RationalInterval)
    (values : ι → ℝ) (h : ∀ i, (boxes i).Encloses (values i)) :
    (product indices boxes).Encloses (indices.map values).prod := by
  induction indices with
  | nil => simpa [product] using point_encloses 1
  | cons i rest ih =>
    simpa only [product, List.foldr_cons, List.map_cons, List.prod_cons] using
      mul_encloses (h i) ih

/-- Rational interval Leibniz expansion in supplied, executable enumeration orders.
The soundness theorem requires both lists to enumerate their domains exactly once. -/
def determinant {n : Type} [Fintype n] [DecidableEq n]
    (indices : List n) (permutations : List (Equiv.Perm n))
    (boxes : Matrix n n RationalInterval) : RationalInterval :=
  sum permutations fun permutation =>
    mul (point ((Equiv.Perm.sign permutation : ℤ) : ℚ))
      (product indices fun i => boxes (permutation i) i)

/-- Every real matrix whose entries are enclosed has its determinant enclosed. -/
theorem determinant_encloses {n : Type} [Fintype n] [DecidableEq n]
    (indices : List n) (permutations : List (Equiv.Perm n))
    (hindices : indices.Nodup) (hindices_all : indices.toFinset = Finset.univ)
    (hpermutations : permutations.Nodup)
    (hpermutations_all : permutations.toFinset = Finset.univ)
    (boxes : Matrix n n RationalInterval) (matrix : Matrix n n ℝ)
    (h : ∀ i j, (boxes i j).Encloses (matrix i j)) :
    (determinant indices permutations boxes).Encloses matrix.det := by
  have summands : ∀ permutation : Equiv.Perm n,
      (mul (point ((Equiv.Perm.sign permutation : ℤ) : ℚ))
        (product indices fun i => boxes (permutation i) i)).Encloses
      (((Equiv.Perm.sign permutation : ℤ) : ℝ) * ∏ i, matrix (permutation i) i) := by
    intro permutation
    have products := product_encloses indices
      (fun i => boxes (permutation i) i) (fun i => matrix (permutation i) i)
      (fun i => h (permutation i) i)
    simpa only [← List.prod_toFinset _ hindices, hindices_all, Rat.cast_intCast] using
      mul_encloses (point_encloses ((Equiv.Perm.sign permutation : ℤ) : ℚ)) products
  have totals := sum_encloses permutations
    (fun permutation => mul (point ((Equiv.Perm.sign permutation : ℤ) : ℚ))
      (product indices fun i => boxes (permutation i) i))
    (fun permutation => ((Equiv.Perm.sign permutation : ℤ) : ℝ) *
      ∏ i, matrix (permutation i) i) summands
  simpa only [determinant, ← List.sum_toFinset _ hpermutations, hpermutations_all,
    ← Matrix.det_apply'] using totals

-- Exact arithmetic checks include crossing zero, two negative intervals, and
-- a degenerate interval. Their proofs reduce rational computations in Lean.
example : mul ⟨-2, 1⟩ ⟨-3, 4⟩ = ⟨-8, 6⟩ := by norm_num [mul, min_def, max_def]
example : mul ⟨-3, -1⟩ ⟨-4, -2⟩ = ⟨2, 12⟩ := by norm_num [mul, min_def, max_def]
example : mul ⟨-2, -2⟩ ⟨1, 3⟩ = ⟨-6, -2⟩ := by norm_num [mul, min_def, max_def]

example (boxes : Matrix (Fin 0) (Fin 0) RationalInterval) :
    determinant [] [Equiv.refl (Fin 0)] boxes = point 1 := by
  simp [determinant, sum, product, mul, add, point]

end RationalInterval

/-- Polynomial expressions, with arbitrary variable index type. -/
inductive PolynomialExpression (ι : Type) where
  | constant (q : ℚ)
  | input (i : ι)
  | neg (p : PolynomialExpression ι)
  | add (p q : PolynomialExpression ι)
  | sub (p q : PolynomialExpression ι)
  | mul (p q : PolynomialExpression ι)
  deriving Repr

namespace PolynomialExpression

def eval {ι : Type} (v : ι → ℝ) : PolynomialExpression ι → ℝ
  | constant q => q
  | input i => v i
  | neg p => -p.eval v
  | add p q => p.eval v + q.eval v
  | sub p q => p.eval v - q.eval v
  | mul p q => p.eval v * q.eval v

def intervalEval {ι : Type} (v : ι → RationalInterval) :
    PolynomialExpression ι → RationalInterval
  | constant q => RationalInterval.point q
  | input i => v i
  | neg p => RationalInterval.neg (p.intervalEval v)
  | add p q => RationalInterval.add (p.intervalEval v) (q.intervalEval v)
  | sub p q => RationalInterval.sub (p.intervalEval v) (q.intervalEval v)
  | mul p q => RationalInterval.mul (p.intervalEval v) (q.intervalEval v)

/-- Structural evaluation is a sound enclosure for real polynomial evaluation. -/
theorem intervalEval_encloses {ι : Type} (p : PolynomialExpression ι)
    (v : ι → ℝ) (boxes : ι → RationalInterval)
    (h : ∀ i, (boxes i).Encloses (v i)) :
    (p.intervalEval boxes).Encloses (p.eval v) := by
  induction p with
  | constant q => exact RationalInterval.point_encloses q
  | input i => exact h i
  | neg p hp => exact RationalInterval.neg_encloses hp
  | add p q hp hq => exact RationalInterval.add_encloses hp hq
  | sub p q hp hq => exact RationalInterval.sub_encloses hp hq
  | mul p q hp hq => exact RationalInterval.mul_encloses hp hq

end PolynomialExpression

#print axioms RationalInterval.mul_encloses
#print axioms RationalInterval.nonzero_of_excludes_zero
#print axioms RationalInterval.determinant_encloses
#print axioms PolynomialExpression.intervalEval_encloses

end GaussianCI
