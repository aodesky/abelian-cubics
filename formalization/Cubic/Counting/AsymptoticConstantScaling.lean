import Cubic.Counting.AsymptoticConstantsData

/-!
# The factors in the passage from Laurent coefficients to `thm:asymptoticPolynomialCount`

This file checks the residue algebra, the polynomial multiplicity `1/2`, the
split-point correction, and the scale change `X = 3 H²`. These are identities
of main terms, independent of the Perron estimate and the polynomial
counting formula. The paper substitutes `X = 3H²+1`; the effect of the `+1`
is estimated in `AsymptoticHeightShift`.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstantScaling

open AsymptoticConstantsData

/-- Main term from the pole of `Z₀(2s)`, retaining the derivative of `1/s`. -/
def coefficientMainTerm (c₂ c₁ : ℂ) (X : ℝ) : ℂ :=
  (c₂ / 4) * X * (Real.log X : ℂ) + (c₁ / 2 - c₂ / 4) * X

/-- Main term after subtracting split points and dividing by two. -/
def toricPolynomialMainTerm (c₂ c₁ : ℂ) (X : ℝ) : ℂ :=
  (c₂ / 8) * X * (Real.log X : ℂ) +
    (c₁ / 4 - c₂ / 8 - (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ))) * X

def rootPolynomialMainTerm (c₂ c₁ : ℂ) (H : ℝ) : ℂ :=
  leadingFromLaurent c₂ * H ^ 2 * (Real.log H : ℂ) +
    (leadingFromLaurent c₂ * (Real.log (Real.sqrt 3) : ℂ) +
      secondaryFromLaurent c₂ c₁ - (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ))) * H ^ 2

/-- The ellipse area enters with coefficient `-1/6`, not `-1/3`. -/
theorem split_subtraction (c₂ c₁ : ℂ) (X : ℝ) :
    (1 / 2 : ℂ) * coefficientMainTerm c₂ c₁ X -
      (1 / 6 : ℂ) * (2 * (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ))) * X =
      toricPolynomialMainTerm c₂ c₁ X := by
  dsimp [coefficientMainTerm, toricPolynomialMainTerm]
  ring

/-- The height rescaling produces `C=3c₂/4`, `D=3(c₁-c₂/2)/4`, and
the final split correction `-π/(3√3)`. -/
theorem height_rescaling (c₂ c₁ : ℂ) (H : ℝ) (hH : 0 < H) :
    toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2) = rootPolynomialMainTerm c₂ c₁ H := by
  have hlog : Real.log (3 * H ^ 2) = Real.log 3 + 2 * Real.log H := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hH.ne'), Real.log_pow]
    norm_num
  simp only [toricPolynomialMainTerm, rootPolynomialMainTerm, hlog,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3), leadingFromLaurent, secondaryFromLaurent]
  push_cast
  ring

end Cubic.Counting.AsymptoticConstantScaling
