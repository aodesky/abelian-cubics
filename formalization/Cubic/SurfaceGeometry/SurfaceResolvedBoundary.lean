import Cubic.SurfaceGeometry.ResolutionFan
import Cubic.SurfaceGeometry.ResolutionPicard
import Cubic.SurfaceGeometry.ResolutionIntersections
import Cubic.SurfaceGeometry.ResolutionPolytopes
import CubicTargets.SurfaceGeometry.SurfaceResolvedBoundary

/-! The canonical fan subdivision and the reduced inverse image of `D₀`.
The entire computation follows the appendix's ray, divisor and polytope argument. -/

namespace Cubic.SurfaceGeometry.SurfaceResolvedBoundary

theorem «prop:surfaceResolvedBoundary» :
    CubicTargets.SurfaceGeometry.SurfaceResolvedBoundary.Claim where
  original_rays := ResolutionFan.original_rays
  complete := ResolutionFan.complete
  smooth := ResolutionFan.smooth
  conjugate_rays := ResolutionFan.conjugate_rays
  conjugate_cones := ResolutionFan.conjugate_cones
  subdivision := ResolutionFan.subdivision
  minimal := ResolutionFan.minimal
  projective_support := ResolutionFan.projective_support
  crepant := ResolutionFan.crepant
  geometric_picard_rank := ResolutionPicard.geometric_picard_rank
  anticanonical_nef := ResolutionIntersections.anticanonical_nef
  anticanonical_big := ResolutionPolytopes.anticanonical_big_iff_positive_square.mpr
    (by rw [ResolutionIntersections.anticanonical_square]; norm_num)
  anticanonical_square := ResolutionIntersections.anticanonical_square
  boundary_pullback := ResolutionFan.pullback_from_original_height
  boundary_support := ResolutionIntersections.boundary_support
  boundary_chain := ResolutionIntersections.boundary_chain
  boundary_chain_intersections := ResolutionIntersections.boundary_chain_intersections
  canonical_boundary := ResolutionIntersections.canonical_boundary
  boundary_square := ResolutionIntersections.boundary_square
  log_square := ResolutionIntersections.log_square
  log_nef := ResolutionIntersections.log_nef
  log_nontrivial := ResolutionIntersections.log_nontrivial
  log_not_big := fun h => by
    have hp := ResolutionPolytopes.log_big_iff_positive_square.mp h
    rw [ResolutionIntersections.log_square] at hp
    omega
  log_big_iff_positive_square := ResolutionPolytopes.log_big_iff_positive_square

end Cubic.SurfaceGeometry.SurfaceResolvedBoundary
