import CubicTargets.BoxAsymptotic.Statement
import Cubic.PoissonSummation.HeightZetaCorrectionProduct

/-! Every assertion of `thm:main`, including the second displayed formula
for the leading constant and the final order-of-growth conclusion. -/

noncomputable section

namespace CubicTargets.BoxAsymptotic

/-- The asymptotic error estimate, both descriptions of its positive leading
constant (`A3` is already defined by the first), and two-sided comparability. -/
def FullMainClaim : Prop :=
  MainClaim ∧
    A3 = 484 * Real.pi / (2187 * Real.sqrt 3) *
      (Cubic.PoissonSummation.HeightZetaCorrectionProduct.value 1).re ∧
    0 < A3 ∧
    ∃ c₁ c₂ H₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ H : ℝ, H₀ ≤ H →
      c₁ * H * Real.log H ^ 3 ≤ (CubicTargets.BoxHeight.boxCount H : ℝ) ∧
      (CubicTargets.BoxHeight.boxCount H : ℝ) ≤ c₂ * H * Real.log H ^ 3

end CubicTargets.BoxAsymptotic
