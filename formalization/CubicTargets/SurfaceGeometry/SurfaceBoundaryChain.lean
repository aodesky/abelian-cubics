import Cubic.SurfaceGeometry.ResolutionData

namespace CubicTargets.SurfaceGeometry.SurfaceBoundaryChain

open Cubic.SurfaceGeometry.ResolutionData

def Claim : Prop :=
  (fun j : Fin 5 => selfIntersection (boundaryOrder j)) = ![-2,-2,-1,-2,-2] ∧
  ∀ i j : Fin 5, intersectionMatrix (boundaryOrder i) (boundaryOrder j) =
    if i = j then selfIntersection (boundaryOrder i)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

end CubicTargets.SurfaceGeometry.SurfaceBoundaryChain
