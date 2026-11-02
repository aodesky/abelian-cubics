import CubicTargets.PoissonSummation.LeadingTerms
import Cubic.Counting.HeightCoefficientData

/-! The bounded Euler-factor comparison inside the proof of
`thm:asymptoticPolynomialCount`. The continuation is Z₀(z)=F(2z).
The constant depends only on η; these segments avoid the pole at 1. -/
noncomputable section
namespace CubicTargets.Counting.HeightMeanBound
open CubicTargets.PoissonSummation.LeadingTerms Cubic.Counting.HeightCoefficientData

def Claim : Prop :=
  ∀ (D F : ℂ → ℂ) (γ c₂ c₁ : ℂ), Expansion D F γ c₂ c₁ →
    ∀ η : ℝ, 0 < η →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : ℝ, 1 / 2 + η ≤ σ → ∀ U : ℝ, 2 ≤ U →
        (∫ t in U..2 * U, ‖F (2 * ((σ : ℂ) + t * Complex.I))‖) ≤
          A * ∫ t in U..2 * U, ‖zetaE ((σ : ℂ) + t * Complex.I)‖ ^ 2

end CubicTargets.Counting.HeightMeanBound
