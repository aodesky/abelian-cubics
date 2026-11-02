import Cubic.Counting.HeightCoefficientData

/-! Uniform strip estimate for the genuine continued quadratic Dedekind zeta
function, written as `zetaE = zeta * L(chi,-)` in the established model. -/

namespace CubicTargets.Counting.XiMeanBound
open Cubic.Counting.HeightCoefficientData

def Claim : Prop := ∀ η : ℝ, 0 < η →
  ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
    ∫ t in U..2 * U, ‖zetaE ((σ : ℂ) + t * Complex.I)‖ ^ 2 ≤ K * U ^ (1 + η)

end CubicTargets.Counting.XiMeanBound
