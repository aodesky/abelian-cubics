import Cubic.SantensComparison.FanData
import Cubic.Counting.IntegralPointCountData
import CubicTargets.SurfaceGeometry.SurfaceResolvedBoundary
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The count in `prop:santensConstant` is the original affine integral-point
count with its original toric height. The additional clauses retain the arithmetic
geometry used in its proof. Its implementation is conditional on the named
general Santens literature input and specializes the fan, metric and measures;
the earlier Poisson asymptotic does not replace that argument. -/

namespace CubicTargets.SantensComparison.SantensConstant

open Cubic.SantensComparison.FanData
open Cubic.Counting.IntegralPointCountData Filter Asymptotics

structure Claim : Prop where
  resolution : SurfaceGeometry.SurfaceResolvedBoundary.Claim
  arithmetic_picard_rank : Module.finrank ℚ ArithmeticPicard = 4
  open_picard : ∃ e : OpenPicard ≃ₗ[ℤ] (ℤ × ℤ),
    ∀ d, e (Submodule.Quotient.mk d) = openProjection d
  adelic_picard : ∃ e : AdelicPicard ≃ₗ[ℤ] (ℤ × ℤ),
    ∀ d, e (Submodule.Quotient.mk d) = adelicProjection d
  units : ∀ m : ℤ × ℤ, (∀ i, pairing m (openRay i) = 0) → m = 0
  regular_functions : ∀ m : ℤ × ℤ,
    (∀ i, 0 ≤ pairing m (openRay i)) → 0 ≤ pairing m 0 → m = 0
  real_face : ∀ A, StableFace A ↔ A = ∅ ∨ A = {0}
  cone_constant : theta = 2
  positive_constant : 0 < alpha
  finite_counts : ∀ B : ℝ, (boundedAffinePoints B).Finite
  estimate : (fun B : ℝ => (affineCount B : ℝ)) ~[atTop]
    (fun B : ℝ => (2 * alpha / 9) * B ^ 2 * Real.log B)

end CubicTargets.SantensComparison.SantensConstant
