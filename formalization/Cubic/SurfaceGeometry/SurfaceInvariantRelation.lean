import CubicTargets.SurfaceGeometry.SurfaceInvariantRelation
import Cubic.ToricHeights.AffineC3Invariants

namespace Cubic.SurfaceGeometry.SurfaceInvariantRelation

open Cubic.ToricHeights.TernaryCyclicInvariants

theorem «eqn:surfaceInvariantRelation» :
    CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim := by
  unfold CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim
  rw [Cubic.ToricHeights.AffineC3Invariants.esymm_one,
    Cubic.ToricHeights.AffineC3Invariants.esymm_two,
    Cubic.ToricHeights.AffineC3Invariants.esymm_three]
  unfold delta
  ring

end Cubic.SurfaceGeometry.SurfaceInvariantRelation
