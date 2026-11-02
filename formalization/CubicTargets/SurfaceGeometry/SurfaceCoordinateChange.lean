import Cubic.SurfaceGeometry.CubicData
import Cubic.SurfaceGeometry.LocalizedCubicData

namespace CubicTargets.SurfaceGeometry.SurfaceCoordinateChange

open Cubic.SurfaceGeometry.CubicData
open Cubic.SurfaceGeometry

structure Claim : Prop where
  inverse_change : ∀ v : Fin 4 → ℚ, inverseCoordinateChange (coordinateChange v) = v
  change_inverse : ∀ x : Fin 4 → ℚ, coordinateChange (inverseCoordinateChange x) = x
  equation_change : ∀ v : Fin 4 → ℚ,
    normCubic (coordinateChange v) = 27 * F (v 0) (v 1) (v 2) (v 3)
  localized_inverse_change :
    LocalizedCubicData.originalToNorm.comp LocalizedCubicData.normToOriginal =
      AlgHom.id LocalizedCubicData.Base LocalizedCubicData.Ambient
  localized_change_inverse :
    LocalizedCubicData.normToOriginal.comp LocalizedCubicData.originalToNorm =
      AlgHom.id LocalizedCubicData.Base LocalizedCubicData.Ambient
  localized_equation_change :
    LocalizedCubicData.normToOriginal LocalizedCubicData.normEquation =
      27 * LocalizedCubicData.originalEquation

end CubicTargets.SurfaceGeometry.SurfaceCoordinateChange
