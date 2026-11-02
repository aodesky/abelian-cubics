import Cubic.SurfaceGeometry.ResolutionData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Cubic.SurfaceGeometry.ResolutionFan

open ResolutionData

theorem original_rays : ambientRay 0 = (-1,-1) ∧ ambientRay 3 = (1,0) ∧
    ambientRay 6 = (0,1) := by norm_num [ambientRay, rays]

theorem smooth (i : Fin 9) : det (rays i) (rays (next i)) = 1 := by
  fin_cases i <;> decide

/-- Galois conjugation exchanges the two coordinates in the (ω,γω) basis. -/
theorem conjugate_rays (i : Fin 9) : rays (-i) = ((rays i).2, (rays i).1) := by
  fin_cases i <;> decide

/-- Conjugation preserves the two-dimensional cones and reverses their order. -/
theorem conjugate_cones (i : Fin 9) : -(next i) = prev (-i) := by
  fin_cases i <;> decide

theorem minimal (i : Fin 9) (hi : i.val % 3 ≠ 0) :
    det (rays (prev i)) (rays (next i)) = 2 := by
  fin_cases i <;> first | contradiction | decide

theorem subdivision (i : Fin 9) :
    (3 : ℤ) • rays i =
      (3 - (i.val % 3 : ℤ)) • rays ⟨3 * (i.val / 3), by omega⟩ +
        (i.val % 3 : ℤ) • rays ⟨(3 * (i.val / 3) + 3) % 9, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases i <;> decide

theorem complete : Complete := by
  intro v
  rcases v with ⟨x,y⟩
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact ⟨4, by simpa [detReal, realRay, rays, next] using hy,
        by simpa [detReal, realRay, rays, next] using hx⟩
    · by_cases h₁ : x ≤ -y
      · refine ⟨1, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
      · by_cases h₂ : x ≤ -2*y
        · refine ⟨2, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
        · refine ⟨3, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
  · by_cases hy : 0 ≤ y
    · by_cases h₁ : -2*x ≤ y
      · refine ⟨5, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
      · by_cases h₂ : -x ≤ y
        · refine ⟨6, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
        · refine ⟨7, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
    · by_cases hxy : x ≤ y
      · refine ⟨8, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith
      · refine ⟨0, ?_, ?_⟩ <;> norm_num [detReal, realRay, rays, next] <;> linarith

theorem projective_support (i : Fin 9) : 0 < curveIntersection ampleDivisor i := by
  fin_cases i <;> decide

/-- The reduced inverse image is taken from the actual original height support
function, rather than choosing a divisor with the desired intersection numbers. -/
theorem pullback_from_original_height (i : Fin 9) :
    (pullbackThreeD0 i : ℝ) =
      -(Cubic.ToricHeights.supportFunction 3 0
        (((ambientRay i).1 : ℝ), ((ambientRay i).2 : ℝ))).re := by
  fin_cases i <;> norm_num [pullbackThreeD0, ambientRay, rays,
    Cubic.ToricHeights.supportFunction]

theorem crepant (i : Fin 9) :
    (antiK i : ℝ) = -(Cubic.ToricHeights.supportFunction 1 1
      (((ambientRay i).1 : ℝ), ((ambientRay i).2 : ℝ))).re := by
  fin_cases i <;> norm_num [antiK, ambientRay, rays, Cubic.ToricHeights.supportFunction]

end Cubic.SurfaceGeometry.ResolutionFan
