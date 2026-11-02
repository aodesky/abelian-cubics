import Cubic.SurfaceGeometry.ResolutionData
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum

namespace Cubic.SurfaceGeometry.ResolutionPicard

open ResolutionData

theorem principal_injective : Function.Injective principal := by
  intro m n h
  have h₁ := congrFun h 4
  have h₂ := congrFun h 5
  simp [principal, rays] at h₁ h₂
  exact Prod.ext h₁ h₂

theorem geometric_picard_rank : Module.finrank ℚ Picard = 7 := by
  have hr := LinearMap.finrank_range_of_inj principal_injective
  have hd := Submodule.finrank_quotient_add_finrank principal.range
  rw [hr] at hd
  norm_num [Module.finrank_prod, Module.finrank_pi] at hd
  change Module.finrank ℚ Picard + 2 = 9 at hd
  omega

end Cubic.SurfaceGeometry.ResolutionPicard
