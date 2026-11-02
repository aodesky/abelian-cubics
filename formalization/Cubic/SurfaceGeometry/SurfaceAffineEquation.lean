import CubicTargets.SurfaceGeometry.SurfaceAffineEquation
import Cubic.SurfaceGeometry.AffineDehomogenization

namespace Cubic.SurfaceGeometry.SurfaceAffineEquation

theorem «eqn:surfaceAffineModel» : CubicTargets.SurfaceGeometry.SurfaceAffineEquation.Claim :=
  ⟨AffineDehomogenization.equation_dehomogenize,
    AffineDehomogenization.presentation, AffineDehomogenization.presentation_mk⟩

end Cubic.SurfaceGeometry.SurfaceAffineEquation
