import Cubic.SurfaceGeometry.ResolutionData

namespace CubicTargets.SurfaceGeometry.SurfaceLogIntersections

open Cubic.SurfaceGeometry.ResolutionData

def Claim : Prop := intersection canonical boundary = -1 ∧
  intersection boundary boundary = -1 ∧ intersection logDivisor logDivisor = 0

end CubicTargets.SurfaceGeometry.SurfaceLogIntersections
