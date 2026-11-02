import Cubic.SurfaceGeometry.RationalSingularities

namespace Cubic.SurfaceGeometry.RationalVertexCharts

open RationalFormData CubicData
open Cubic.QuadraticCorrespondence.CyclotomicField

variable {k : Type*} [Field k]

theorem chart_equation (i : Fin 3) (u : Fin 3 → k) :
    splitCubic (vertexChart i u) = u 0 * u 1 - u 2 ^ 3 := by
  fin_cases i <;> simp [splitCubic,vertexChart]

theorem coordinates_chart (i : Fin 3) (u : Fin 3 → k) :
    vertexCoordinates i (vertexChart i u) = u := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [vertexChart,vertexCoordinates]

theorem chart_coordinates (i : Fin 3) (x : Fin 4 → k)
    (hx : x ⟨i.val,by omega⟩ = 1) : vertexChart i (vertexCoordinates i x) = x := by
  funext j
  fin_cases i <;> fin_cases j <;> simp_all [vertexChart,vertexCoordinates]

theorem chart_origin (i : Fin 3) : vertexChart (k := k) i 0 = splitVertex i := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [vertexChart,splitVertex]

theorem split_boundary (x : Fin 4 → k) (hx : splitCubic x = 0) :
    x 3 = 0 ↔ x 0 = 0 ∨ x 1 = 0 ∨ x 2 = 0 := by
  have h : x 0 * x 1 * x 2 = x 3 ^ 3 := sub_eq_zero.mp hx
  rw [← pow_eq_zero_iff (n := 3) (by decide), ← h, mul_eq_zero, mul_eq_zero, or_assoc]

theorem rational_singularity (x : Fin 4 → ℚ) :
    NormSingular ℚ x ↔ ∃ c : ℚ, c ≠ 0 ∧ x = c • splitVertex 0 := by
  constructor
  · rintro ⟨hx,_,hg⟩
    have hN : x 1 ^ 2 + 3 * x 2 ^ 2 = 0 := by
      simpa only [RationalSingularities.norm_gradient] using hg 0
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 2),sq_nonneg (x 1)]
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 2)]
    have h3 : x 3 = 0 := by
      simpa [RationalSingularities.norm_gradient] using hg 3
    have h0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      funext i
      fin_cases i <;> simp [h0,h1,h2,h3]
    refine ⟨x 0,h0,?_⟩
    funext i
    fin_cases i <;> simp [splitVertex,h1,h2,h3]
  · rintro ⟨c,hc,rfl⟩
    refine ⟨?_,?_,?_⟩
    · intro h
      exact hc (by simpa [splitVertex] using congrFun h 0)
    · simp [normCubic,splitVertex]
    · intro i
      rw [RationalSingularities.norm_gradient]
      fin_cases i <;> simp [splitVertex]

theorem conjugate_pair :
    (fun j => conjugation (singularVector 1 j)) = singularVector 2 := by
  funext j
  fin_cases j <;> simp [singularVector,normVertex,conjugation_sqrtNegThree]

theorem rational_fixed :
    (fun j => conjugation (singularVector 0 j)) = singularVector 0 := by
  funext j
  fin_cases j <;> simp [singularVector,normVertex]

theorem singularities_distinct (i j : Fin 3) (c : E) (hc : c ≠ 0)
    (h : singularVector i = c • singularVector j) : i = j := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have hr := sqrtNegThree_ne_zero
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals first
    | (change (1 : E) = c * 0 at h0
       exact (one_ne_zero (h0.trans (mul_zero c))).elim)
    | (change (0 : E) = c * 1 at h0
       exact (hc ((mul_one c).symm.trans h0.symm)).elim)
    | (change (1 : E) = c * 1 at h2
       have hc1 : c = 1 := (mul_one c).symm.trans h2.symm
       subst c
       have he : sqrtNegThree = -sqrtNegThree := by
         first
         | exact (show sqrtNegThree = (1 : E) * -sqrtNegThree from h1).trans (one_mul _)
         | exact ((show -sqrtNegThree = (1 : E) * sqrtNegThree from h1).trans (one_mul _)).symm
       have hz : (2 : E) * sqrtNegThree = 0 := by linear_combination he
       exact ((mul_ne_zero (by norm_num) hr) hz).elim)

end Cubic.SurfaceGeometry.RationalVertexCharts
