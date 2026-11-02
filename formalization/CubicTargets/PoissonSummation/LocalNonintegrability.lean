import CubicTargets.PoissonSummation.HeightFourierTransform

namespace CubicTargets.PoissonSummation.LocalNonintegrability

open MeasureTheory CubicTargets.PoissonSummation.HeightFourierTransform
open Cubic.ToricHeights
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology Cubic.ToricHeights.QuotientLocalHaar

/-- The paper assumes Γ-invariant parameters, so `s₁=s₂=σ`.
At `σ=0` integrability fails for every finite prime other than three,
regardless of `s₀`. -/
structure Claim : Prop where
  split : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (s₀ : ℂ),
    ¬ Integrable (splitIntegrand p s₀ 0) (QuotientLocalHaar.splitMeasure p)
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (s₀ : ℂ),
    ¬ Integrable (inertIntegrand p s₀ 0) (QuotientLocalHaar.inertMeasure p)

end CubicTargets.PoissonSummation.LocalNonintegrability
