import CubicTargets.SurfaceGeometry.SurfaceCoordinateChange
import Cubic.SurfaceGeometry.RationalFormData
import Cubic.QuadraticCorrespondence.CyclotomicConjugation

namespace CubicTargets.Introduction.SplitForm

open Cubic.SurfaceGeometry RationalFormData CubicData
open Cubic.QuadraticCorrespondence.CyclotomicField

/-- The original cubic is identified with its norm form over `ℚ`, and
with the displayed split form over the actual field `ℚ(√−3)`. -/
def Claim : Prop :=
  CubicTargets.SurfaceGeometry.SurfaceCoordinateChange.Claim ∧
  (∃ e : (Fin 4 → E) ≃ₗ[E] (Fin 4 → E),
    (∀ x, e x = splitChange sqrtNegThree x) ∧
    (∀ x, e.symm x = inverseSplitChange sqrtNegThree x) ∧
    ∀ x, splitCubic (e x) = normCubic x)

end CubicTargets.Introduction.SplitForm
