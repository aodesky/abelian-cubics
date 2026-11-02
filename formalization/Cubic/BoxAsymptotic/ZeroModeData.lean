import CubicTargets.BoxAsymptotic.Statement
import Cubic.PoissonSummation.QuadraticZetaRegularization
import Cubic.PoissonSummation.HeightZetaCorrectionProduct
import Mathlib.NumberTheory.LSeries.Basic

/-! Canonical objects in `eq:F0`. The series is defined from the actual congruence
conditions, independently of the proposed Euler product. -/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroModeData

open CubicTargets.BoxAsymptotic Cubic.PoissonSummation

/-- The total mass of the angular counting measure. -/
def mass (n : ℕ) : ℝ := muIntegral n (fun _ => 1)

/-- The original Dirichlet series; as usual `LSeries` omits the term at zero. -/
def series (s : ℂ) : ℂ := LSeries (fun n => (mass n : ℂ)) s

/-- The local factor multiplying `ζ_E(s)² R(s)` in `eq:F0`. -/
def localFactor (s : ℂ) : ℂ :=
  (1 / 3) * (1 + 2 * (3 : ℂ) ^ (-(2 * s))) * (1 - (3 : ℂ) ^ (-s))

/-- Proposed continuation, subsequently identified with the independently defined series. -/
def continuation (s : ℂ) : ℂ :=
  localFactor s * QuadraticZetaRegularization.value s ^ 2 *
    HeightZetaCorrectionProduct.value s

/-- Its regularized analytic numerator at the double pole. -/
def numerator (s : ℂ) : ℂ :=
  localFactor s * QuadraticZetaRegularization.regular s ^ 2 *
    HeightZetaCorrectionProduct.value s

/-- The real lower Laurent coefficient. Its identification is a conclusion, not an assumption. -/
def b₀ : ℝ := (deriv numerator 1).re

end Cubic.BoxAsymptotic.ZeroModeData
