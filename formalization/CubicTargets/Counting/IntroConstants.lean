import Cubic.Counting.IntegralPointCountData
import CubicTargets.Counting.AsymptoticPolynomialCount

namespace CubicTargets.Counting.IntroConstants

open Cubic.Counting.IntegralPointCountData
open Cubic.Counting.AsymptoticConstantsData Cubic.PoissonSummation.FiniteEulerProduct

/-- The constants in the introduction, with existence of the defining limit and
absolute convergence of the displayed product and sum. -/
def Claim : Prop := ∃ (Z : ℂ → ℂ) (μ : ℂ),
  AsymptoticPolynomialCount.EulerKronecker Z μ ∧
  alpha = ∏' p : SplitPrimes, (1 - 2 / ((p.1 : ℝ) * ((p.1 : ℝ) + 1))) ∧
  beta = ∑' p : SplitPrimes,
    ((2 * (p.1 : ℝ) + 1) * Real.log p.1 / (((p.1 : ℝ) ^ 2 - 1) * ((p.1 : ℝ) + 2))) ∧
  Summable (fun p : SplitPrimes => ‖simplifiedSplitFactor p - 1‖) ∧
  Summable (fun p : SplitPrimes => ‖simplifiedSplitLogTerm p‖) ∧
  0 < alpha

end CubicTargets.Counting.IntroConstants
