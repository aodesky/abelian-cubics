import Cubic.SurfaceGeometry.AffineModelData
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace CubicTargets.SurfaceGeometry.SurfaceAffineModel

open Cubic.SurfaceGeometry Cubic.SurfaceGeometry.AffineModelData
open Cubic.SurfaceGeometry.CubicPresentationData

structure Claim : Prop where
  dehomogenization : dehomogenize cubic = equation ℤ
  chart_presentation : ∃ e : (CubicRing ⧸ normalizedChartIdeal) ≃ₐ[ℤ] CoordinateRing ℤ,
    ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (dehomogenize p)
  original_invariants : ∃ e : CoordinateRing ℤ ≃ₐ[ℤ]
      Cubic.ToricHeights.AffineInvariantRing.invariants,
    ∀ p, (e (Ideal.Quotient.mk _ p)).val = invariantEvaluation p
  global_integrality : ∀ P : CoordinateRing ℤ →+* ℚ,
    (∀ f, ∃ z : ℤ, P f = z) ↔
      (∃ a : ℤ, P (coordinate ℤ 0) = a) ∧ (∃ b : ℤ, P (coordinate ℤ 1) = b)
  local_integrality : ∀ (p : ℕ) [Fact p.Prime] (P : CoordinateRing ℤ →+* ℚ_[p]),
    (∀ f, ‖P f‖ ≤ 1) ↔ ‖P (coordinate ℤ 0)‖ ≤ 1 ∧ ‖P (coordinate ℤ 1)‖ ≤ 1

end CubicTargets.SurfaceGeometry.SurfaceAffineModel
