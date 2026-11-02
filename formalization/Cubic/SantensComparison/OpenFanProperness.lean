import Cubic.SantensComparison.FanArithmetic

/-! The support criterion for the proper toric map U → S\D₀. The open
subfan consists of the three smooth cones on the four retained rays; their
union is exactly the original affine cone. These are the actual cones, not
just a count of rays in the subdivision. -/

namespace Cubic.SantensComparison.OpenFanProperness

open Cubic.SurfaceGeometry.ResolutionData FanData

def cone (i : Fin 9) : Set (ℝ × ℝ) :=
  {v | 0 ≤ detReal (realRay i) v ∧ 0 ≤ detReal v (realRay (next i))}

def affineCone : Set (ℝ × ℝ) :=
  {v | 0 ≤ detReal (realRay 3) v ∧ 0 ≤ detReal v (realRay 6)}

theorem retained_cones (i : Fin 9) :
    boundary i=0 ∧ boundary (next i)=0 ↔ i=3 ∨ i=4 ∨ i=5 := by
  fin_cases i <;> decide

theorem proper_support : (⋃ i : {i : Fin 9 // boundary i=0 ∧ boundary (next i)=0},
    cone i.val) = affineCone := by
  ext v
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,hv⟩
    rcases (retained_cones i).mp hi with rfl | rfl | rfl <;>
      norm_num [cone, affineCone, detReal, realRay, rays, next] at * <;>
      constructor <;> linarith
  · intro hv
    have h : 0 ≤ v.1+2*v.2 ∧ 0 ≤ 2*v.1+v.2 := by
      simpa [affineCone, detReal, realRay, rays, mul_comm, add_comm] using hv
    by_cases hy : v.2 ≤ 0
    · refine ⟨⟨3,by decide⟩,?_⟩
      norm_num [cone, detReal, realRay, rays, next]
      constructor <;> linarith
    · by_cases hx : 0 ≤ v.1
      · refine ⟨⟨4,by decide⟩,?_⟩
        norm_num [cone, detReal, realRay, rays, next]
        exact ⟨by linarith,hx⟩
      · refine ⟨⟨5,by decide⟩,?_⟩
        norm_num [cone, detReal, realRay, rays, next]
        constructor <;> linarith

end Cubic.SantensComparison.OpenFanProperness
