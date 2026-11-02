import CubicTargets.PoissonSummation.LeadingTerms
import Cubic.Counting.IntegralPointCountData

namespace CubicTargets.PoissonSummation.Z0Laurent

open Filter Asymptotics Cubic.Counting.IntegralPointCountData
open scoped Topology

/-- Every continuation supplied by the leading-term proposition has the
manuscript's Laurent expansion in the squared-height variable z. -/
def Claim : Prop := ∀ (D F : ℂ → ℂ) (μ c₂ c₁ : ℂ),
  LeadingTerms.Expansion D F μ c₂ c₁ →
    (fun z : ℂ => F (2 * z) - (alpha : ℂ) / (9 * (z - 1) ^ 2) -
      (2 * (alpha : ℂ) / 9) * (μ - deriv riemannZeta 2 / riemannZeta 2 +
        (beta : ℂ) + 3 / 8 * (Real.log 3 : ℂ)) / (z - 1))
      =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ))

end CubicTargets.PoissonSummation.Z0Laurent
