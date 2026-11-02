import CubicTargets.PoissonSummation.LeadingTerms
import CubicTargets.Counting.AsymptoticPolynomialCount
import Cubic.PoissonSummation.EulerCorrectionData
import Cubic.Counting.IntegralPointCountData

namespace CubicTargets.PoissonSummation.LeadingTermsNormalized

open Filter Asymptotics Cubic.Counting.IntegralPointCountData
open scoped Topology

/-- `prop:leadingTerms` in the manuscript's squared-height variable `z`.
The function agrees with the original point-counting series on its convergence
half-plane. Both the pole order and the explicit bounded Laurent remainder are
part of the conclusion. -/
def Claim : Prop := ∃ (D F : ℂ → ℂ) (μ : ℂ),
  CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker D μ ∧
  (∀ z : ℂ, 1 < z.re → F z = Cubic.PoissonSummation.EulerCorrectionData.Z0 z) ∧
  MeromorphicOn F {z : ℂ | (1 / 2 : ℝ) < z.re} ∧
  (∀ z : ℂ, (1 / 2 : ℝ) < z.re → z ≠ 1 → AnalyticAt ℂ F z) ∧
  meromorphicOrderAt F 1 = (-2 : ℤ) ∧
  (fun z : ℂ => F z - (alpha : ℂ) / (9 * (z - 1) ^ 2) -
    (2 * (alpha : ℂ) / 9) * (μ - deriv riemannZeta 2 / riemannZeta 2 +
      (beta : ℂ) + 3 / 8 * (Real.log 3 : ℂ)) / (z - 1))
    =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ))

end CubicTargets.PoissonSummation.LeadingTermsNormalized
