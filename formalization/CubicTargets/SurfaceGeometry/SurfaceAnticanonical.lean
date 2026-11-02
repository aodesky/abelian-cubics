import Cubic.SurfaceGeometry.CubicAdjunctionData
import Cubic.SurfaceGeometry.HyperplaneIntersectionData
import Cubic.SurfaceGeometry.BoundaryMultiplicity

/-! The adjunction, Cartier-section and intersection computations for
eqn:surfaceAnticanonical. The dual complex uses actual ambient top forms;
both intersection lengths use the original cubic equation. -/

namespace CubicTargets.SurfaceGeometry.SurfaceAnticanonical

open Cubic.SurfaceGeometry
open CubicAdjunctionData HypersurfaceDualityData

structure Claim : Prop where
  equation_nonzero : equation ≠ 0
  equation_degree : Homogeneous ℚ equation 3
  free_resolution : Function.Injective (multiplication ℚ equation) ∧
    LinearMap.range (multiplication ℚ equation) =
      LinearMap.ker (Ideal.span {equation}).mkQ
  canonical_twist : ∃ e : CanonicalModule ≃ₗ[Ambient ℚ] CoordinateRing,
    ∀ n x, CanonicalDegree n x ↔ CoordinateDegree (n - 1) (e x)
  boundary_support : BoundaryData.hyperplaneIdeal.radical = BoundaryData.lineIdeal
  boundary_equation : BoundaryMultiplicity.sectionPolynomial = Polynomial.X ^ 3
  boundary_multiplicity : Module.finrank BoundaryMultiplicity.BoundaryField
    BoundaryMultiplicity.genericSection = 3
  generic_line_avoids_infinity : HyperplaneIntersectionData.infinityValue ≠ 0
  hyperplane_square : Module.finrank HyperplaneIntersectionData.ParameterField
    HyperplaneIntersectionData.IntersectionRing = 3

end CubicTargets.SurfaceGeometry.SurfaceAnticanonical
