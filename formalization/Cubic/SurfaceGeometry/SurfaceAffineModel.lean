import CubicTargets.SurfaceGeometry.SurfaceAffineModel
import Cubic.SurfaceGeometry.SurfaceAffineEquation
import Cubic.SurfaceGeometry.AffineInvariantPresentation
import Cubic.SurfaceGeometry.AffineModelIntegrality

namespace Cubic.SurfaceGeometry.SurfaceAffineModel

theorem «prop:surfaceAffineModel» : CubicTargets.SurfaceGeometry.SurfaceAffineModel.Claim where
  dehomogenization := SurfaceAffineEquation.«eqn:surfaceAffineModel».1
  chart_presentation := SurfaceAffineEquation.«eqn:surfaceAffineModel».2
  original_invariants := ⟨AffineInvariantPresentation.presentation,
    AffineInvariantPresentation.presentation_mk⟩
  global_integrality := AffineModelIntegrality.global_integrality
  local_integrality := AffineModelIntegrality.local_integrality

end Cubic.SurfaceGeometry.SurfaceAffineModel
