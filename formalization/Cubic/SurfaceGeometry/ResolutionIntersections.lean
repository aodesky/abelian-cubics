import Cubic.SurfaceGeometry.ResolutionData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Cubic.SurfaceGeometry.ResolutionIntersections

open ResolutionData

theorem anticanonical_nef : Nef antiK := by intro i; fin_cases i <;> decide
theorem log_nef : Nef logDivisor := by intro i; fin_cases i <;> decide

theorem anticanonical_square : intersection antiK antiK = 3 := by decide
theorem canonical_boundary : intersection canonical boundary = -1 := by decide
theorem boundary_square : intersection boundary boundary = -1 := by decide
theorem log_square : intersection logDivisor logDivisor = 0 := by decide

theorem boundary_support (i : Fin 9) :
    boundary i = if 0 < pullbackThreeD0 i then 1 else 0 := by
  fin_cases i <;> decide

theorem boundary_chain :
    (fun j : Fin 5 => selfIntersection (boundaryOrder j)) = ![-2,-2,-1,-2,-2] := by
  decide

theorem boundary_chain_intersections (i j : Fin 5) :
    intersectionMatrix (boundaryOrder i) (boundaryOrder j) =
      if i = j then selfIntersection (boundaryOrder i)
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

theorem log_nontrivial : ∃ i, curveIntersection logDivisor i ≠ 0 :=
  ⟨2, by decide⟩

/-- Principal character divisors have zero intersection with every invariant curve. -/
theorem principal_curve_zero (m : ℤ × ℤ) (i : Fin 9) :
    curveIntersection (fun j => m.1 * (rays j).1 + m.2 * (rays j).2) i = 0 := by
  fin_cases i <;>
    norm_num [curveIntersection, selfIntersection, det, rays, prev, next] <;> ring

end Cubic.SurfaceGeometry.ResolutionIntersections
