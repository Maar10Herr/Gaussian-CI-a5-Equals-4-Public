module

public import GaussianCI.Cycle
public import GaussianCI.Coverage
public import GaussianCI.Interval
public import GaussianCI.Finite
public import GaussianCI.Generated
public import GaussianCI.WorkedWitness
public import GaussianCI.Krawczyk
public import GaussianCI.Minimality
public import GaussianCI.PolynomialDerivative
public import GaussianCI.FaceWitnesses

/-!
# Partial formalization of the Gaussian CI threshold argument

This library proves concrete matrix implications and witnesses, finite checks,
and analytic certificate infrastructure. It does not yet prove the complete
three-antecedent classification or instantiate the conditional threshold theorem
for every Gaussian rule. In particular it does not establish `a_5 = 4` in Lean.
-/
