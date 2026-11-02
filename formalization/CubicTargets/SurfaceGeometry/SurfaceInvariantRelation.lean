import Cubic.SurfaceGeometry.InvariantCubicData

namespace CubicTargets.SurfaceGeometry.SurfaceInvariantRelation

open Cubic.ToricHeights.TernaryCyclicInvariants

def Claim : Prop :=
  delta ^ 2 - (e 1 * e 2 - 3 * e 3) * delta +
    e 2 ^ 3 + e 1 ^ 3 * e 3 - 6 * e 1 * e 2 * e 3 + 9 * e 3 ^ 2 = 0

end CubicTargets.SurfaceGeometry.SurfaceInvariantRelation
