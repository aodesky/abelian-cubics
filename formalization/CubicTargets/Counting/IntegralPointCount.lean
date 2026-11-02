import Cubic.Counting.IntegralPointCountData
import CubicTargets.Counting.AsymptoticPolynomialCount

/-! Exact target for `cor:integralPointCount`, including the original point set,
every positive error exponent, and the displayed polynomial `Q`. -/

namespace CubicTargets.Counting.IntegralPointCount

open Filter Asymptotics Cubic.Counting.IntegralPointCountData
open Cubic.Counting.AsymptoticConstantsData Cubic.PoissonSummation.FiniteEulerProduct

structure Asymptotic (μ : ℂ) : Prop where
  /-- No affine integral point is omitted by computing the height on the torus. -/
  affine_comparison : ∀ P : Cubic.ToricHeights.AffineChartInvariants.RationalPoint,
    Cubic.ToricHeights.AffineChartInvariants.IsD0Integral P →
      ∃! Q : Cubic.PoissonSummation.AdelicHeightZetaData.RationalPoints,
        Q.toRingHom.comp
          Cubic.ToricHeights.AffineInvariantRing.invariantRestriction.toRingHom = P
  finite_counts : ∀ H : ℝ, (boundedAffinePoints H).Finite
  estimate : ∀ ε : ℝ, 0 < ε →
    (fun H : ℝ => (affineCount H : ℝ) - H ^ 2 * Q μ (Real.log H))
      =O[atTop] (fun H : ℝ => H ^ (1 + ε))

def Claim : Prop := ∃ (Z : ℂ → ℂ) (μ : ℂ),
  AsymptoticPolynomialCount.EulerKronecker Z μ ∧
  Summable (fun p : SplitPrimes => ‖simplifiedSplitFactor p - 1‖) ∧
  Summable (fun p : SplitPrimes => ‖simplifiedSplitLogTerm p‖) ∧
  0 < alpha ∧ Asymptotic μ

end CubicTargets.Counting.IntegralPointCount
