import CubicTargets.SurfaceGeometry.SurfaceIntegralCubic
import Cubic.SurfaceGeometry.CubicGrading
import Cubic.SurfaceGeometry.SurfaceAnticanonical

/-! The paper's order: invariant normal form and third Veronese; homogeneous
cubic presentation and projective charts;
boundary line, multiplicity and hypersurface adjunction. -/

namespace Cubic.SurfaceGeometry.SurfaceIntegralCubic

theorem «prop:surfaceIntegralCubic» :
    CubicTargets.SurfaceGeometry.SurfaceIntegralCubic.Claim where
  cubic_homogeneous := CubicGrading.cubic_homogeneous
  cubic_degree := CubicGrading.cubic_degree
  presentation := ⟨CubicPresentation.presentation, CubicPresentation.presentation_mk⟩
  graded_evaluation := fun _ _ => CubicGrading.evaluation_homogeneous
  graded_surjectivity := CubicGrading.homogeneous_preimage
  projective_charts := ProjectiveCharts.veronese_chart
  boundary_line := ⟨BoundaryLine.presentation, by
    intro p
    simp only [BoundaryLine.presentation, AlgEquiv.trans_apply,
      Ideal.quotientEquivAlgOfEq_mk]
    rfl⟩
  boundary_prime := BoundaryLine.line_prime
  boundary_support := BoundaryLine.reduced_hyperplane
  anticanonical := SurfaceAnticanonical.«eqn:surfaceAnticanonical»

end Cubic.SurfaceGeometry.SurfaceIntegralCubic
