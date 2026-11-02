import Cubic.ToricHeights.AffineInvariantRing

/-! A rational point of `T` is `D₀`-integral (every regular function of the integral
affine chart is integer-valued) iff the coefficients `a` and `b` of its characteristic
polynomial `t³ - t² + at - b` are integers. -/

namespace CubicTargets.ToricHeights.AffineIntegralPoints

open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.ToricHeights

/-- Integrality of every integral invariant function is equivalent to integrality of the
two coefficients. -/
def Claim : Prop := ∀ P : quotientFixedRing →ₐ[ℚ] ℚ,
  AffineInvariantRing.IntegralPoint P ↔
    (∃ a : ℤ, P linearCoefficient = (a : ℚ)) ∧
    (∃ b : ℤ, P constantCoefficient = (b : ℚ))

end CubicTargets.ToricHeights.AffineIntegralPoints
