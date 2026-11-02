import Cubic.SurfaceGeometry.ResolutionData
import Cubic.SurfaceGeometry.ResolutionIntersections
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Cubic.SurfaceGeometry.ResolutionPolytopes

open ResolutionData

theorem anticanonical_big : Big antiK := by
  let V : Set (ℝ × ℝ) := Set.Ioo (-1/4) (1/4) ×ˢ Set.Ioo (-1/4) (1/4)
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_Ioo
  have hsub : V ⊆ polytope antiK := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ i
    fin_cases i <;> norm_num [antiK, rays] <;> linarith [hx.1, hx.2, hy.1, hy.2]
  refine ⟨(0,0), interior_mono hsub ?_⟩
  rw [hV.interior_eq]
  norm_num [V]

theorem log_polytope (m : ℝ × ℝ) :
    m ∈ polytope logDivisor ↔ m.1 = m.2 ∧ -1 ≤ m.1 ∧ m.1 ≤ 0 := by
  constructor
  · intro h
    have h₁ := h 1
    have h₂ := h 2
    have h₄ := h 4
    have h₇ := h 7
    norm_num [logDivisor, antiK, boundary, rays] at h₁ h₂ h₄ h₇
    exact ⟨by linarith, h₄, by linarith⟩
  · rintro ⟨he,hlo,hhi⟩ i
    fin_cases i <;> norm_num [logDivisor, antiK, boundary, rays] <;> linarith

theorem log_not_big : ¬ Big logDivisor := by
  rintro ⟨m,hm⟩
  have he := (log_polytope m).mp (interior_subset hm)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hm)
  have hmem : (m.1 + ε/2, m.2) ∈ Metric.ball m ε := by
    rw [Metric.mem_ball]
    change dist (m.1 + ε/2, m.2) (m.1,m.2) < ε
    rw [dist_prod_same_right, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (by linarith : 0 < ε/2)]
    linarith
  have hnew := (log_polytope (m.1 + ε/2,m.2)).mp (hball hmem)
  dsimp at hnew
  linarith [he.1, hnew.1]

/-- Verify the appendix's nef-square criterion on its actual anticanonical divisor. -/
theorem anticanonical_big_iff_positive_square :
    Big antiK ↔ 0 < intersection antiK antiK := by
  rw [ResolutionIntersections.anticanonical_square]
  exact ⟨fun _ => by norm_num, fun _ => anticanonical_big⟩

/-- Verify the nef-square criterion on the actual log divisor from the reduced boundary.
The independent polytope calculation checks this specialization without an
additional geometric input. -/
theorem log_big_iff_positive_square :
    Big logDivisor ↔ 0 < intersection logDivisor logDivisor := by
  rw [ResolutionIntersections.log_square]
  exact ⟨fun h => False.elim (log_not_big h), fun h => False.elim (by omega)⟩

end Cubic.SurfaceGeometry.ResolutionPolytopes
