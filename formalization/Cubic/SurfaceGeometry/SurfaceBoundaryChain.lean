import Cubic.SurfaceGeometry.ResolutionIntersections
import CubicTargets.SurfaceGeometry.SurfaceBoundaryChain

namespace Cubic.SurfaceGeometry.SurfaceBoundaryChain

theorem «eqn:surfaceBoundaryChain» :
    CubicTargets.SurfaceGeometry.SurfaceBoundaryChain.Claim :=
  ⟨ResolutionIntersections.boundary_chain, ResolutionIntersections.boundary_chain_intersections⟩

end Cubic.SurfaceGeometry.SurfaceBoundaryChain
