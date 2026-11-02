import Cubic.AllGaloisCounts.SliceYIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute integrability and the change of integration order in the
slice-volume calculation. The integral uses the actual intersection length. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceFubini
open CountData LinearFactorSlice SlicePieces SliceYIntegral MeasureTheory

theorem F_bounds (x y : ℝ) : 0 ≤ F x y ∧ F x y ≤ 2 := by
  by_cases hx : x = 0
  · simp [hx, F]
  · rw [length_formula hx]
    refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    have h1 := min_le_left (x ^ 2 + x * y + 1) |x|⁻¹
    have h2 := le_max_left (x ^ 2 + x * y - 1) (-|x|⁻¹)
    linarith

theorem norm_F_le (x y : ℝ) : ‖F x y‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (F_bounds x y).1]
  exact (F_bounds x y).2

theorem measurable_F : Measurable (fun p : ℝ × ℝ => F p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => F p.1 p.2) =
      (fun p => if p.1 = 0 then 2 else
        max (min (p.1 ^ 2 + p.1 * p.2 + 1) |p.1|⁻¹ -
          max (p.1 ^ 2 + p.1 * p.2 - 1) (-|p.1|⁻¹)) 0) := by
    funext p
    by_cases hp : p.1 = 0
    · simp [hp, F]
    · simp only [if_neg hp, length_formula hp]
  rw [he]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const
  fun_prop

theorem rectangle_integrable (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.Ioc (-1) 1))) := by
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
    ⟨by simp only [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    ⟨by simp only [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact (integrable_const (2 : ℝ)).mono' measurable_F.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => norm_F_le p.1 p.2))

theorem J_intervalIntegrable (a b : ℝ) : IntervalIntegrable J volume a b := by
  rw [intervalIntegrable_iff]
  change Integrable (fun x => ∫ y in (-1 : ℝ)..1, F x y)
    (volume.restrict (Set.uIoc a b))
  have h := (rectangle_integrable a b).integral_prod_left
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h

theorem J_even : Function.Even J := by
  intro x
  simp only [J, reflect]
  simpa using (intervalIntegral.integral_comp_neg
    (f := fun y => F x y) (a := -1) (b := 1))

theorem volume_half : (∫ y in (-1 : ℝ)..1, g y) = 2 * ∫ x in (0 : ℝ)..vartheta, J x := by
  have hp : 0 < vartheta := by linarith [vartheta_spec.1]
  have hs : (∫ y in (-1 : ℝ)..1, g y) = ∫ x in -vartheta..vartheta, J x := by
    calc _ = ∫ y in (-1 : ℝ)..1, ∫ x in -vartheta..vartheta, F x y := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
          intro y hy
          exact integral_compact hy
      _ = _ := by
          have hi := rectangle_integrable (-vartheta) vartheta
          rw [Set.uIoc_of_le (by linarith)] at hi
          simp only [J, intervalIntegral.integral_of_le (show -vartheta ≤ vartheta by linarith),
            intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
          exact (integral_integral_swap hi).symm
  rw [hs, ← intervalIntegral.integral_add_adjacent_intervals
    (J_intervalIntegrable (-vartheta) 0) (J_intervalIntegrable 0 vartheta)]
  have hn : (∫ x in -vartheta..0, J x) = ∫ x in (0 : ℝ)..vartheta, J x := by
    calc _ = ∫ x in (0 : ℝ)..vartheta, J (-x) := by
          simpa using (intervalIntegral.integral_comp_neg (f := J) (a := 0) (b := vartheta)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x _
        exact J_even x
  rw [hn]
  ring

end Cubic.AllGaloisCounts.SliceFubini
