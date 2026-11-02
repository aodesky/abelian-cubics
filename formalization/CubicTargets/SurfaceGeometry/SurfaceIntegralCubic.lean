import Cubic.SurfaceGeometry.CubicPresentationData
import Cubic.SurfaceGeometry.ProjectiveCharts
import CubicTargets.SurfaceGeometry.SurfaceAnticanonical

/-! Integral cubic model in its homogeneous-coordinate and projective-chart
description. The embedding is certified by the standard graded cubic quotient.
The Veronese chart comparison takes place in their common fraction field. -/

namespace CubicTargets.SurfaceGeometry.SurfaceIntegralCubic

open MvPolynomial Cubic.SurfaceGeometry
open CubicPresentationData VeroneseData ProjectiveChartData
open Cubic.ToricHeights.TernaryCyclicInvariants

structure Claim : Prop where
  cubic_homogeneous : cubic.IsHomogeneous 3
  cubic_degree : cubic.totalDegree = 3
  presentation : ∃ e : (CubicRing ⧸ Ideal.span {cubic}) ≃ₐ[ℤ] thirdVeronese,
    ∀ p, (e (Ideal.Quotient.mk _ p)).val = cubicEvaluation p
  graded_evaluation : ∀ n p, p.IsHomogeneous n →
    (cubicEvaluation p).IsHomogeneous (3 * n)
  graded_surjectivity : ∀ n (f : thirdVeronese), f.val.IsHomogeneous (3 * n) →
    ∃ p : CubicRing, p.IsHomogeneous n ∧ cubicEvaluation p = f.val
  projective_charts : ∀ (f : invariants) d, f.val.IsHomogeneous d → f ≠ 0 →
    Chart f d = VeroneseChart f d
  boundary_line : ∃ e : (CubicRing ⧸ BoundaryData.lineIdeal) ≃ₐ[ℤ]
      MvPolynomial (Fin 2) ℤ,
    ∀ p, e (Ideal.Quotient.mk _ p) = BoundaryData.restriction p
  boundary_prime : BoundaryData.lineIdeal.IsPrime
  boundary_support : BoundaryData.hyperplaneIdeal.radical = BoundaryData.lineIdeal
  anticanonical : SurfaceAnticanonical.Claim

end CubicTargets.SurfaceGeometry.SurfaceIntegralCubic
