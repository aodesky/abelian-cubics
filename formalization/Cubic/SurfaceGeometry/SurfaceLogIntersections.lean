import Cubic.SurfaceGeometry.ResolutionIntersections
import CubicTargets.SurfaceGeometry.SurfaceLogIntersections

namespace Cubic.SurfaceGeometry.SurfaceLogIntersections

theorem «eqn:surfaceLogIntersections» :
    CubicTargets.SurfaceGeometry.SurfaceLogIntersections.Claim :=
  ⟨ResolutionIntersections.canonical_boundary, ResolutionIntersections.boundary_square,
    ResolutionIntersections.log_square⟩

end Cubic.SurfaceGeometry.SurfaceLogIntersections
