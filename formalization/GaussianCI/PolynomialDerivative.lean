module

public import GaussianCI.Interval
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Exact polynomial differentiation and interval Jacobians

Symbolic partial differentiation of the rational polynomial expression language
is connected to the real Fréchet derivative. Evaluating the differentiated
expressions on rational intervals therefore encloses each entry of the actual
Jacobian on the box.

This module does not identify the expressions with the certificate files or
establish a Krawczyk inclusion or a root-existence certificate.
-/

@[expose] public section

namespace GaussianCI
namespace PolynomialExpression

/-- Executable symbolic differentiation with respect to a single input. -/
def partialDerivative {ι : Type} [DecidableEq ι] (i : ι) :
    PolynomialExpression ι → PolynomialExpression ι
  | constant _ => constant 0
  | input j => constant (if i = j then 1 else 0)
  | neg p => neg (partialDerivative i p)
  | add p q => add (partialDerivative i p) (partialDerivative i q)
  | sub p q => sub (partialDerivative i p) (partialDerivative i q)
  | mul p q => add (mul p (partialDerivative i q)) (mul q (partialDerivative i p))

/-- The continuous linear map supplied by the real differentiation rules. -/
noncomputable def differential {ι : Type} [Fintype ι]
    (p : PolynomialExpression ι) (v : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  match p with
  | constant _ => 0
  | input i => ContinuousLinearMap.proj i
  | neg p => -p.differential v
  | add p q => p.differential v + q.differential v
  | sub p q => p.differential v - q.differential v
  | mul p q => p.eval v • q.differential v + q.eval v • p.differential v

/-- Every expression has the Fréchet derivative obtained by structural rules. -/
theorem hasFDerivAt_eval {ι : Type} [Fintype ι]
    (p : PolynomialExpression ι) (v : ι → ℝ) :
    HasFDerivAt (fun x => p.eval x) (p.differential v) v := by
  induction p with
  | constant q => exact hasFDerivAt_const (q : ℝ) v
  | input i => exact hasFDerivAt_apply i v
  | neg p hp => exact hp.neg
  | add p q hp hq => exact hp.add hq
  | sub p q hp hq => exact hp.sub hq
  | mul p q hp hq => exact hp.mul hq

/-- A symbolic partial equals the Fréchet derivative in its coordinate direction. -/
theorem partial_eval_eq_differential_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : PolynomialExpression ι) (v : ι → ℝ) (i : ι) :
    (partialDerivative i p).eval v = p.differential v (Pi.single i 1) := by
  induction p with
  | constant q => simp [partialDerivative, eval, differential]
  | input j =>
    by_cases hij : i = j <;>
      simp [partialDerivative, eval, differential, hij, eq_comm]
  | neg p hp => simp [partialDerivative, eval, differential, hp]
  | add p q hp hq => simp [partialDerivative, eval, differential, hp, hq]
  | sub p q hp hq => simp [partialDerivative, eval, differential, hp, hq]
  | mul p q hp hq => simp [partialDerivative, eval, differential, hp, hq]

theorem fderiv_eval_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : PolynomialExpression ι) (v : ι → ℝ) (i : ι) :
    fderiv ℝ (fun x => p.eval x) v (Pi.single i 1) = (partialDerivative i p).eval v := by
  rw [(hasFDerivAt_eval p v).fderiv]
  exact (partial_eval_eq_differential_basis p v i).symm

/-- Interval evaluation of a symbolic partial encloses the actual derivative. -/
theorem intervalPartial_encloses {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : PolynomialExpression ι) (v : ι → ℝ) (boxes : ι → RationalInterval)
    (h : ∀ i, (boxes i).Encloses (v i)) (i : ι) :
    ((partialDerivative i p).intervalEval boxes).Encloses
      (fderiv ℝ (fun x => p.eval x) v (Pi.single i 1)) := by
  rw [fderiv_eval_basis]
  exact intervalEval_encloses (partialDerivative i p) v boxes h

/-- Entrywise rational interval evaluation of the symbolic Jacobian. -/
def intervalJacobian {m n : Type} [DecidableEq n]
    (system : m → PolynomialExpression n) (boxes : n → RationalInterval) :
    Matrix m n RationalInterval :=
  fun i j => (partialDerivative j (system i)).intervalEval boxes

/-- The real derivative of the entire polynomial system. -/
noncomputable def systemDifferential {m n : Type} [Fintype m] [Fintype n]
    (system : m → PolynomialExpression n) (v : n → ℝ) :
    (n → ℝ) →L[ℝ] (m → ℝ) :=
  ContinuousLinearMap.pi fun i => (system i).differential v

theorem hasFDerivAt_system {m n : Type} [Fintype m] [Fintype n]
    (system : m → PolynomialExpression n) (v : n → ℝ) :
    HasFDerivAt (fun x i => (system i).eval x) (systemDifferential system v) v := by
  exact hasFDerivAt_pi.mpr fun i => hasFDerivAt_eval (system i) v

theorem system_fderiv_basis {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (system : m → PolynomialExpression n) (v : n → ℝ) (i : m) (j : n) :
    (fderiv ℝ (fun x i => (system i).eval x) v (Pi.single j 1)) i =
      (partialDerivative j (system i)).eval v := by
  rw [(hasFDerivAt_system system v).fderiv]
  exact (partial_eval_eq_differential_basis (system i) v j).symm

/-- Every entry encloses the corresponding entry of the true system derivative. -/
theorem intervalJacobian_encloses_fderiv {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n]
    (system : m → PolynomialExpression n) (v : n → ℝ) (boxes : n → RationalInterval)
    (h : ∀ j, (boxes j).Encloses (v j)) (i : m) (j : n) :
    (intervalJacobian system boxes i j).Encloses
      ((fderiv ℝ (fun x i => (system i).eval x) v (Pi.single j 1)) i) := by
  rw [system_fderiv_basis]
  exact intervalEval_encloses (partialDerivative j (system i)) v boxes h

#print axioms hasFDerivAt_eval
#print axioms partial_eval_eq_differential_basis
#print axioms intervalPartial_encloses
#print axioms hasFDerivAt_system
#print axioms intervalJacobian_encloses_fderiv

end PolynomialExpression
end GaussianCI
