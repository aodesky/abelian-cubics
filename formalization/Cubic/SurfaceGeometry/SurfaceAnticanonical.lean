import CubicTargets.SurfaceGeometry.SurfaceAnticanonical
import Cubic.SurfaceGeometry.CubicAdjunction
import Cubic.SurfaceGeometry.HyperplaneIntersection

namespace Cubic.SurfaceGeometry.SurfaceAnticanonical

theorem «eqn:surfaceAnticanonical» :
    CubicTargets.SurfaceGeometry.SurfaceAnticanonical.Claim where
  equation_nonzero := CubicAdjunction.equation_ne_zero
  equation_degree := CubicAdjunction.equation_homogeneous
  free_resolution := CubicAdjunction.free_resolution_exact
  canonical_twist := ⟨CubicAdjunction.adjunction, CubicAdjunction.adjunction_degree⟩
  boundary_support := BoundaryLine.reduced_hyperplane
  boundary_equation := BoundaryMultiplicity.section_equation
  boundary_multiplicity := BoundaryMultiplicity.generic_length
  generic_line_avoids_infinity := HyperplaneIntersection.infinity_ne_zero
  hyperplane_square := HyperplaneIntersection.generic_length

end Cubic.SurfaceGeometry.SurfaceAnticanonical
