import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.ZMod.Basic

/-!
# Polynomials in the cyclotomic correspondence

These definitions record the exact rational cubic, inverse quadratic,
Galois-or-split condition, and ordinary integral-coefficient condition from
`prop:cyclotomicParametrization`. They do not identify a cubic with the
characteristic polynomial of a geometric point.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CorrespondencePolynomials

open Polynomial

/-- The paper's monic trace-one cubic, as a polynomial. -/
def cubic (a b : ℚ) : ℚ[X] := X ^ 3 - X ^ 2 + C a * X + C b

/-- The inverse quadratic appearing in the proposition. Its use requires
the nonvanishing of `1-3a`. -/
def inverseQuadratic (a b : ℚ) : ℚ[X] :=
  X ^ 2 - C (3 - (1 + 27 * b) / (1 - 3 * a)) * X + C (1 - 3 * a)

/-- Galois group exactly cyclic of order three, using the splitting field. -/
def HasCyclicCubicGaloisGroup (f : ℚ[X]) : Prop :=
  Nonempty (f.Gal ≃* Multiplicative (ZMod 3))

/-- The paper's admissible polynomials: cyclic cubic or rationally split,
with the triple-root case excluded. -/
def Admissible (f : ℚ[X]) : Prop :=
  (HasCyclicCubicGaloisGroup f ∨ f.Splits) ∧
    ¬ ∃ r : ℚ, f = (X - C r) ^ 3

/-- Every coefficient belongs to the image of the integers in the rationals. -/
def HasIntegralCoefficients (f : ℚ[X]) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, f.coeff n = (z : ℚ)

end Cubic.QuadraticCorrespondence.CorrespondencePolynomials
