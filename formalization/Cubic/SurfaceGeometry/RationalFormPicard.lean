import Cubic.SurfaceGeometry.RationalFormData
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum

namespace Cubic.SurfaceGeometry.RationalFormPicard

open RationalFormData

theorem simplicial (i : Fin 3) :
    ResolutionData.det (originalRay i) (originalRay (i+1)) = 3 := by
  fin_cases i <;> decide

theorem complete (v : ℝ × ℝ) : ∃ i : Fin 3,
    0 ≤ ResolutionData.detReal ((originalRay i).1,(originalRay i).2) v ∧
    0 ≤ ResolutionData.detReal v ((originalRay (i+1)).1,(originalRay (i+1)).2) := by
  rcases v with ⟨x,y⟩
  have hnext : (2 : Fin 3)+1=0 := by decide
  have hnext1 : (1 : Fin 3)+1=2 := by decide
  by_cases h1 : 0 ≤ x+2*y
  · by_cases h2 : 0 ≤ 2*x+y
    · refine ⟨1,?_,?_⟩ <;>
        norm_num [hnext1,ResolutionData.detReal,originalRay,ResolutionData.rays] <;> linarith
    · refine ⟨2,?_,?_⟩ <;>
        norm_num [hnext,ResolutionData.detReal,originalRay,ResolutionData.rays] <;> linarith
  · by_cases h0 : y ≤ x
    · refine ⟨0,?_,?_⟩ <;>
        norm_num [hnext,ResolutionData.detReal,originalRay,ResolutionData.rays] <;> linarith
    · refine ⟨2,?_,?_⟩ <;>
        norm_num [hnext,ResolutionData.detReal,originalRay,ResolutionData.rays] <;> linarith

theorem principal_injective : Function.Injective principal := by
  intro m n h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  norm_num [principal, originalRay, ResolutionData.rays] at h₀ h₁
  apply Prod.ext <;> linarith

theorem geometric_picard_rank : Module.finrank ℚ Picard = 1 := by
  have hr := LinearMap.finrank_range_of_inj principal_injective
  have hd := Submodule.finrank_quotient_add_finrank principal.range
  rw [hr] at hd
  norm_num [Module.finrank_prod, Module.finrank_pi] at hd
  change Module.finrank ℚ Picard + 2 = 3 at hd
  omega

end Cubic.SurfaceGeometry.RationalFormPicard
