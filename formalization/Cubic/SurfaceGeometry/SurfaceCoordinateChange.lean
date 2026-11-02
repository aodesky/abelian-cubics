import CubicTargets.SurfaceGeometry.SurfaceCoordinateChange
import Cubic.SurfaceGeometry.LocalizedCubicPresentation
import Mathlib.Tactic.FinCases

namespace Cubic.SurfaceGeometry.SurfaceCoordinateChange

open CubicData

theorem inverse_change {R : Type*} [Field R] [CharZero R] (v : Fin 4 → R) :
    inverseCoordinateChange (coordinateChange v) = v := by
  ext i
  fin_cases i <;> simp [coordinateChange, inverseCoordinateChange] <;> ring

theorem change_inverse {R : Type*} [Field R] [CharZero R] (x : Fin 4 → R) :
    coordinateChange (inverseCoordinateChange x) = x := by
  ext i
  fin_cases i <;> simp [coordinateChange, inverseCoordinateChange] <;> ring

theorem equation_change {R : Type*} [Field R] [CharZero R] (v : Fin 4 → R) :
    normCubic (coordinateChange v) = 27 * F (v 0) (v 1) (v 2) (v 3) := by
  simp [normCubic, coordinateChange, F]
  ring

theorem «eqn:surfaceCoordinateChange» :
    CubicTargets.SurfaceGeometry.SurfaceCoordinateChange.Claim where
  inverse_change := inverse_change
  change_inverse := change_inverse
  equation_change := equation_change
  localized_inverse_change := LocalizedCubicPresentation.backward_forward
  localized_change_inverse := LocalizedCubicPresentation.forward_backward
  localized_equation_change := LocalizedCubicPresentation.forward_equation

end Cubic.SurfaceGeometry.SurfaceCoordinateChange
