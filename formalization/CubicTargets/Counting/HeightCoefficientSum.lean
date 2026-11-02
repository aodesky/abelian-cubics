import Cubic.Counting.IntegralPointCountData
import CubicTargets.PoissonSummation.LeadingTerms
import Cubic.PoissonSummation.HeightCountingData

/-!
# `eqn:dSummatoryForGeneralTrace`

For every `ε > 0`,
`Σ_{n ≤ X} d_n = (c₂/4) X log X + (c₁/2 − c₂/4) X + O_ε(X^{1/2+ε})`.

`d_n = HeightCountingData.count n` are the Dirichlet coefficients of
`Z₀(s) = Σ d_n n^{-s}`. Internally, `c₂, c₁` are the
Laurent coefficients of the height series `Z₀(s/2)` at `s = 2` from `prop:leadingTerms`. The statement is
quantified over every witness of `Expansion`, which pins `c₂, c₁` to the Laurent
expansion of the continuation of the original height series. Since `d_0 = 0`,
summing over `1 ≤ n ≤ ⌊X⌋` is the paper's `Σ_{n ≤ X}`.
-/

noncomputable section

namespace CubicTargets.Counting.HeightCoefficientSum

open CubicTargets.PoissonSummation.LeadingTerms

def CoefficientClaim : Prop :=
  ∀ (D F : ℂ → ℂ) (γ c₂ c₁ : ℂ), Expansion D F γ c₂ c₁ →
    ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (Cubic.PoissonSummation.HeightCountingData.count n : ℂ)) -
          (c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X)‖ ≤ K * X ^ (1 / 2 + ε)

/-- The current manuscript's formula in terms of its polynomial `Q`. -/
def Claim : Prop :=
  ∀ (D F : ℂ → ℂ) (μ c₂ c₁ : ℂ), Expansion D F μ c₂ c₁ →
    ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (Cubic.PoissonSummation.HeightCountingData.count n : ℂ)) -
          ((X * Cubic.Counting.IntegralPointCountData.Q μ (1 / 2 * Real.log X) : ℝ) : ℂ)‖ ≤
        K * X ^ (1 / 2 + ε)

end CubicTargets.Counting.HeightCoefficientSum
