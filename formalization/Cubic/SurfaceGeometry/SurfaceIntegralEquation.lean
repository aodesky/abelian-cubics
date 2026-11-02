import Cubic.SurfaceGeometry.SurfaceInvariantRelation
import CubicTargets.SurfaceGeometry.SurfaceIntegralEquation

namespace Cubic.SurfaceGeometry.SurfaceIntegralEquation

open CubicData InvariantCubicData Cubic.ToricHeights.TernaryCyclicInvariants

theorem «eqn:surfaceIntegralCubic» :
    CubicTargets.SurfaceGeometry.SurfaceIntegralEquation.Claim := by
  have h := SurfaceInvariantRelation.«eqn:surfaceInvariantRelation»
  unfold CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim at h
  unfold CubicTargets.SurfaceGeometry.SurfaceIntegralEquation.Claim F A B C D
  linear_combination e 1 ^ 3 * h

end Cubic.SurfaceGeometry.SurfaceIntegralEquation
