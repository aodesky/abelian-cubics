import Cubic.Counting.IntegralPointCountData
import CubicTargets.Counting.WeightedPolynomialCount
import CubicTargets.PoissonSummation.LeadingTerms

/-!
# `eqn:irrPolys`

`Σ_{f ∈ F, H(f) ≤ √X} 1 = (c₂/8) X log X + (c₁/4 − c₂/8 − π/(9√3)) X + O_ε(X^{1/2+ε})`.

`c₂, c₁` are the Laurent coefficients from any witness of `prop:leadingTerms`. `H(f)`
and the counted set are those of `eqn:weightedPolynomialCount`. Finiteness of the
counted set is part of the conclusion.
-/

noncomputable section

namespace CubicTargets.Counting.IrrPolys

open CubicTargets.PoissonSummation.LeadingTerms CubicTargets.Counting.WeightedPolynomialCount

def CoefficientClaim : Prop :=
  ∀ (D F : ℂ → ℂ) (γ c₂ c₁ : ℂ), Expansion D F γ c₂ c₁ →
    ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (countSet (Real.sqrt X)).Finite ∧
        ‖(Nat.card (countSet (Real.sqrt X)) : ℂ) -
            (c₂ / 8 * X * Real.log X +
              (c₁ / 4 - c₂ / 8 - ((Real.pi / (9 * Real.sqrt 3) : ℝ) : ℂ)) * X)‖ ≤
          K * X ^ (1 / 2 + ε)

/-- The current manuscript's formula in terms of its polynomial `Q`. -/
def Claim : Prop :=
  ∀ (D F : ℂ → ℂ) (μ c₂ c₁ : ℂ), Expansion D F μ c₂ c₁ →
    ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (countSet (Real.sqrt X)).Finite ∧
        ‖(Nat.card (countSet (Real.sqrt X)) : ℂ) -
          ((1 / 2 * X * Cubic.Counting.IntegralPointCountData.Q μ (1 / 2 * Real.log X) -
            Real.pi / (9 * Real.sqrt 3) * X : ℝ) : ℂ)‖ ≤ K * X ^ (1 / 2 + ε)

end CubicTargets.Counting.IrrPolys
