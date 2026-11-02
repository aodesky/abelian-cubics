import Cubic.SurfaceGeometry.QuadraticTwistData

namespace CubicTargets.Introduction.SurfaceQuadraticTwist

open Cubic.SurfaceGeometry QuadraticTwistData RationalFormData CubicData
attribute [-instance] DivisionRing.toRatAlgebra

/-- The explicit quadratic field, linear projective change, equation and
descent cocycle for `eqn:surfaceQuadraticTwist`. -/
def Claim : Prop :=
  ∀ d : ℚ, ∀ (_ : Fact (¬ IsSquare d)),
    Module.finrank ℚ (Extension d) = 2 ∧
    root d ^ 2 = algebraMap ℚ (Extension d) d ∧
    conjugation d (root d) = -root d ∧
    (∃ e : (Fin 4 → Extension d) ≃ₗ[Extension d] (Fin 4 → Extension d),
      (∀ x, e x = splitChange (root d) x) ∧
      (∀ x, e.symm x = inverseSplitChange (root d) x)) ∧
    (∀ x : Fin 4 → Extension d,
      splitCubic (splitChange (root d) x) =
        twistCubic (algebraMap ℚ (Extension d) d) x) ∧
    (∀ x : Fin 4 → Extension d,
      (fun i => conjugation d (splitChange (root d) x i)) =
        swapCoordinates (splitChange (root d) (fun i => conjugation d (x i)))) ∧
    (∀ x : Fin 4 → Extension d, splitCubic (swapCoordinates x) = splitCubic x)

end CubicTargets.Introduction.SurfaceQuadraticTwist
