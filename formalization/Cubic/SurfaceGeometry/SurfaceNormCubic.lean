import CubicTargets.SurfaceGeometry.SurfaceNormCubic
import Cubic.SurfaceGeometry.RationalCubicPresentation
import Cubic.SurfaceGeometry.LocalizedCubicPresentation

namespace Cubic.SurfaceGeometry.SurfaceNormCubic

theorem «eqn:surfaceNormCubic» : CubicTargets.SurfaceGeometry.SurfaceNormCubic.Claim where
  localized_presentation :=
    ⟨LocalizedCubicPresentation.presentation, LocalizedCubicPresentation.presentation_mk⟩
  localized_homogeneous := fun _ _ hp =>
    ⟨LocalizedCubicPresentation.forward_homogeneous hp,
      LocalizedCubicPresentation.backward_homogeneous hp⟩
  presentation := ⟨RationalCubicPresentation.presentation,RationalCubicPresentation.presentation_mk⟩
  homogeneous := fun _ _ hp =>
    ⟨RationalCubicPresentation.forward_homogeneous hp,RationalCubicPresentation.backward_homogeneous hp⟩

end Cubic.SurfaceGeometry.SurfaceNormCubic
