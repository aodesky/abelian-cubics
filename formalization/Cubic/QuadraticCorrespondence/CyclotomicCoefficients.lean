import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The paper's cyclotomic coefficient expressions

These are the explicit norm, trace and cubic coefficient expressions from
`prop:cyclotomicParametrization`. Their identification with the coefficients
of the characteristic polynomial of a quotient point is `RationalCoefficientFormula`.
-/

namespace Cubic.QuadraticCorrespondence.CyclotomicCoefficients

variable {R : Type*} [CommRing R]

def normForm (u v : R) : R := u ^ 2 + v ^ 2 - u * v

def traceForm (u v : R) : R := 2 * u - v

/-- The product of the two split embeddings is the cyclotomic norm form. -/
theorem linear_mul_conjugate (ζ u v : R) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (u + v * ζ) * (u + v * (-1 - ζ)) = normForm u v := by
  unfold normForm
  linear_combination -(v ^ 2) * hζ

/-- The sum of the two split embeddings is the cyclotomic trace form. -/
theorem linear_add_conjugate (ζ u v : R) :
    (u + v * ζ) + (u + v * (-1 - ζ)) = traceForm u v := by
  unfold traceForm
  ring

variable {K : Type*} [Field K]

/-- The coefficient of `t` in the paper's monic trace-one cubic. -/
def linearCoefficient (u v : K) : K := (1 - normForm u v) / 3

/-- The constant coefficient of that cubic; it is the negative of `e₃`. -/
def constantCoefficient (u v : K) : K := (normForm u v * (3 - traceForm u v) - 1) / 27

end Cubic.QuadraticCorrespondence.CyclotomicCoefficients
