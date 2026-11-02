import CubicTargets.SurfaceGeometry.SurfaceRationalForm
import Cubic.SurfaceGeometry.SurfaceNormCubic
import Cubic.SurfaceGeometry.SurfaceIntegralCubic
import Cubic.SurfaceGeometry.SurfaceCoordinateChange
import Cubic.SurfaceGeometry.RationalFormSplitting
import Cubic.SurfaceGeometry.RationalFormPicard
import Cubic.SurfaceGeometry.RationalVertexCharts

namespace Cubic.SurfaceGeometry.SurfaceRationalForm

/-- The paper's direct coordinate change, vertex charts,
anticanonical embedding, divisor quotient, and boundary equations. -/
theorem «prop:surfaceRationalForm» : CubicTargets.SurfaceGeometry.SurfaceRationalForm.Claim where
  localized_coordinate_ring := SurfaceNormCubic.«eqn:surfaceNormCubic».localized_presentation
  localized_graded_coordinates := SurfaceNormCubic.«eqn:surfaceNormCubic».localized_homogeneous
  coordinate_change := SurfaceCoordinateChange.«eqn:surfaceCoordinateChange»
  coordinate_ring := SurfaceNormCubic.«eqn:surfaceNormCubic».presentation
  graded_coordinates := SurfaceNormCubic.«eqn:surfaceNormCubic».homogeneous
  anticanonical_embedding := SurfaceIntegralCubic.«prop:surfaceIntegralCubic»
  geometric_picard_rank := RationalFormPicard.geometric_picard_rank
  simplicial_fan := RationalFormPicard.simplicial
  complete_fan := RationalFormPicard.complete
  split_equation := fun _ _ _ => RationalFormSplitting.splitting_equation
  split_inverse := fun _ _ _ r hr =>
    ⟨RationalFormSplitting.split_inverse r hr,RationalFormSplitting.inverse_split r hr⟩
  split_singularities := fun _ _ _ => RationalSingularities.split_singular_locus
  norm_singularities := fun _ _ _ => RationalSingularities.norm_singular_locus
  rational_singularity := RationalVertexCharts.rational_singularity
  singularities_distinct := RationalVertexCharts.singularities_distinct
  conjugate_pair := RationalVertexCharts.conjugate_pair
  rational_fixed := RationalVertexCharts.rational_fixed
  local_A2 := fun _ _ i => ⟨RationalVertexCharts.chart_equation i,
    RationalVertexCharts.coordinates_chart i,RationalVertexCharts.chart_coordinates i,
    RationalVertexCharts.chart_origin i⟩
  boundary := RationalFormSplitting.boundary

end Cubic.SurfaceGeometry.SurfaceRationalForm
