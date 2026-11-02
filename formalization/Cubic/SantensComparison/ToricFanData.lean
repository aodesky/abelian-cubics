import Cubic.SantensComparison.OpenFanProperness
import Cubic.SurfaceGeometry.ResolutionFan

/-! Cyclic two-dimensional fans in the actual cocharacter lattice. The
intersection condition explicitly checks common faces, so completeness and
smooth neighboring cones cannot inadvertently encode a multiple traversal
or overlapping fan. The cubic resolution instantiates all of these laws. -/

namespace Cubic.SantensComparison.ToricFanData

open Cubic.SurfaceGeometry.ResolutionData (det detReal)

structure Fan where
  size : ℕ
  size_pos : 0 < size
  ray : Fin size → ℤ × ℤ

namespace Fan

def next (F : Fan) (i : Fin F.size) : Fin F.size :=
  ⟨(i.val+1)%F.size,Nat.mod_lt _ F.size_pos⟩

def realRay (F : Fan) (i : Fin F.size) : ℝ × ℝ := ((F.ray i).1,(F.ray i).2)

def cone (F : Fan) (i : Fin F.size) : Set (ℝ × ℝ) :=
  {v | 0 ≤ detReal (F.realRay i) v ∧ 0 ≤ detReal v (F.realRay (F.next i))}

def rayCone (F : Fan) (i : Fin F.size) : Set (ℝ × ℝ) :=
  {v | detReal (F.realRay i) v=0 ∧
    0 ≤ (F.realRay i).1*v.1+(F.realRay i).2*v.2}

def commonFace (F : Fan) (i j : Fin F.size) : Set (ℝ × ℝ) :=
  if i=j then F.cone i else if F.next i=j then F.rayCone j
  else if F.next j=i then F.rayCone i else {0}

structure SmoothComplete (F : Fan) : Prop where
  smooth : ∀ i, det (F.ray i) (F.ray (F.next i))=1
  complete : ∀ v, ∃ i, v ∈ F.cone i
  intersections : ∀ i j, F.cone i ∩ F.cone j=F.commonFace i j

end Fan

def paperFan : Fan := ⟨9,by decide,Cubic.SurfaceGeometry.ResolutionData.rays⟩

theorem paper_ray (i : Fin 9) : paperFan.ray i=Cubic.SurfaceGeometry.ResolutionData.rays i := rfl

set_option maxHeartbeats 2000000 in
theorem paper_intersections (i j : Fin 9) :
    paperFan.cone i ∩ paperFan.cone j=paperFan.commonFace i j := by
  ext ⟨x,y⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [Fan.cone, Fan.commonFace, Fan.rayCone, Fan.realRay, Fan.next,
      paper_ray, paperFan, Cubic.SurfaceGeometry.ResolutionData.rays, detReal,
      Set.mem_inter_iff, Prod.mk.injEq] <;>
    constructor <;> intro h <;> (repeat' constructor) <;> linarith

theorem paper_smooth_complete : paperFan.SmoothComplete where
  smooth := Cubic.SurfaceGeometry.ResolutionFan.smooth
  complete := Cubic.SurfaceGeometry.ResolutionFan.complete
  intersections := paper_intersections

end Cubic.SantensComparison.ToricFanData
