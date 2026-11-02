import CubicTargets.Introduction.IdealParametrization
import CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum
import Cubic.Counting.IntegralPointCountData
import Cubic.Counting.PolynomialCountData
import Cubic.Counting.EulerKroneckerCalculation

namespace CubicTargets.Introduction.IdealRemark

open Filter Asymptotics Cubic.Counting
open Cubic.Introduction.CubeIdealSumData
open Cubic.Introduction.EisensteinPointData
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.PoissonSummation.CyclotomicIntegerUnits

/-- The displayed series identity, including its convergence and the bridges
to the full affine locus and the manuscript's condition on ideals. -/
structure SeriesIdentity : Prop where
  fullAffine : ∃ e : IntegralAffine ≃ IntegralTorus,
    ∀ P, Cubic.ToricHeights.AffinePointComparison.restrictPoint (e P).1 = P.1
  idealCondition : ∀ I : Ideal Integers,
    (¬ 3 ∣ Ideal.absNorm I) ↔
      I ⊔ Ideal.span {(3 : Integers)} = ⊤
  pointSeries_absolute : ∀ s : ℂ, 2 < s.re →
    Summable (fun P : IntegralTorus => ‖(pointHeight P : ℂ) ^ (-s)‖)
  idealSeries_absolute : ∀ s : ℂ, 2 < s.re →
    Summable (fun J : CubeIdeals => ‖(Ideal.absNorm J.1 : ℂ) ^ (-s / 6)‖)
  series : ∀ s : ℂ, 2 < s.re →
    (∑' P : IntegralTorus, (pointHeight P : ℂ) ^ (-s)) =
      ∑' J : CubeIdeals, (Ideal.absNorm J.1 : ℂ) ^ (-s / 6)

/-- The actual point and cyclic-polynomial counts with the sharper cited error. -/
structure SharpEstimate : Prop where
  integral_finite : ∀ H : ℝ, (IntegralPointCountData.boundedAffinePoints H).Finite
  cyclic_finite : ∀ H : ℝ, (PolynomialCountData.boundedPolynomials H).Finite
  integral_estimate :
    (fun H : ℝ => (IntegralPointCountData.affineCount H : ℝ) -
      H ^ 2 * IntegralPointCountData.Q EulerKroneckerCalculation.value (Real.log H))
      =O[atTop] heightError
  cyclic_estimate :
    (fun H : ℝ => (PolynomialCountData.polynomialCount H : ℝ) -
      (AsymptoticConstantsData.originalLeading * H ^ 2 * Real.log H +
        (AsymptoticConstantsData.originalLeading * Real.log (Real.sqrt 3) +
          AsymptoticConstantsData.originalLeading * AsymptoticConstantsData.originalSecondaryRatio -
          Real.pi / (3 * Real.sqrt 3)) * H ^ 2))
      =O[atTop] heightError

/-- The series identity and the sharper alternative counting result.
The proof takes only the independently stated Kühleitner--Nowak input. -/
def Claim : Prop := SeriesIdentity ∧ SharpEstimate

end CubicTargets.Introduction.IdealRemark
