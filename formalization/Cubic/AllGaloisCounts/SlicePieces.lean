import Cubic.AllGaloisCounts.SliceRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The three pieces of the actual slice, including their endpoints and
uniform support. These are the moving intervals used in the paper. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SlicePieces
open CountData LinearFactorSlice SliceThresholds Filter MeasureTheory
open scoped Topology

theorem parameter_domain {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    y ∈ Set.Ioo (-2) 2 := ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem neg_parameter {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    -y ∈ Set.Icc (-1) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩

theorem crossing_antitone {y z t : ℝ} (hy : y ∈ Set.Ioo (-2) 2)
    (hz : z ∈ Set.Ioo (-2) 2) (ht : t ∈ Set.Icc 0 2) (hyz : y ≤ z) :
    crossing t z ≤ crossing t y := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hp := crossing_pos hy ht
  have h := strictAnti_psi hz.1 hp (crossing_pos hz ht) hlt
  change psi (crossing t z) z < psi (crossing t y) z at h
  rw [(crossing_spec hz ht).2] at h
  have he := (crossing_spec hy ht).2
  dsimp [psi] at h he
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hyz)]

theorem bounds {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    vartheta⁻¹ ≤ minus y ∧ minus y ≤ 1 ∧ 1 ≤ plus y ∧ plus y ≤ vartheta := by
  have hd := parameter_domain hy
  have h1 : (1 : ℝ) ∈ Set.Ioo (-2) 2 := by norm_num
  have hn : (-1 : ℝ) ∈ Set.Ioo (-2) 2 := by norm_num
  have ht0 : (0 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have ht2 : (2 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have h2a := crossing_antitone hd h1 ht2 hy.2
  have h2b := crossing_antitone hn hd ht2 hy.1
  have h0a := crossing_antitone hd h1 ht0 hy.2
  have h0b := crossing_antitone hn hd ht0 hy.1
  change minus 1 ≤ minus y at h2a
  change minus y ≤ minus (-1) at h2b
  change plus 1 ≤ plus y at h0a
  change plus y ≤ plus (-1) at h0b
  simp only [endpoints.1, endpoints.2.1, endpoints.2.2.1,
    endpoints.2.2.2] at h2a h2b h0a h0b
  exact ⟨h2a, h2b, h0a, h0b⟩

theorem before {x y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (hx : 0 ≤ x) (hxm : x ≤ minus y) : F x y = 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [F]
  have hd := parameter_domain hy
  have ht : (2 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have h := (strictAnti_psi hd.1).antitoneOn hx (crossing_pos hd ht) hxm
  rw [(crossing_spec hd ht).2] at h
  rw [clipped hx hy.1, max_eq_right (by linarith), min_eq_left h]

theorem middle {x y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (hxm : minus y ≤ x) (hxp : x ≤ plus y) : F x y = psi x y := by
  have hd := parameter_domain hy
  have ht0 : (0 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have ht2 : (2 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have hm := crossing_pos hd ht2
  have hp := crossing_pos hd ht0
  have hx : 0 < x := lt_of_lt_of_le hm hxm
  have ha := (strictAnti_psi hd.1).antitoneOn hm hx hxm
  have hb := (strictAnti_psi hd.1).antitoneOn hx hp hxp
  rw [(crossing_spec hd ht2).2] at ha
  rw [(crossing_spec hd ht0).2] at hb
  rw [clipped hx hy.1, max_eq_right hb, min_eq_right ha]

theorem after {x y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (hxp : plus y ≤ x) : F x y = 0 := by
  have hd := parameter_domain hy
  have ht : (0 : ℝ) ∈ Set.Icc 0 2 := by norm_num
  have hp := crossing_pos hd ht
  have hx : 0 < x := lt_of_lt_of_le hp hxp
  have h := (strictAnti_psi hd.1).antitoneOn hp hx hxp
  rw [(crossing_spec hd ht).2] at h
  rw [clipped hx hy.1, max_eq_left h]
  norm_num

theorem near_zero {x y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (hx : |x| ≤ vartheta⁻¹) : F x y = 2 := by
  by_cases hp : 0 ≤ x
  · exact before hy hp ((abs_of_nonneg hp ▸ hx).trans (bounds hy).1)
  · have hn : 0 ≤ -x := by linarith
    have hxn : -x ≤ vartheta⁻¹ := by
      simpa only [abs_of_neg (lt_of_not_ge hp)] using hx
    rw [← neg_neg x, reflect]
    exact before (neg_parameter hy) hn (hxn.trans (bounds (neg_parameter hy)).1)

theorem outside {x y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (hx : vartheta ≤ |x|) : F x y = 0 := by
  by_cases hp : 0 ≤ x
  · exact after hy ((bounds hy).2.2.2.trans (abs_of_nonneg hp ▸ hx))
  · rw [← neg_neg x, reflect]
    exact after (neg_parameter hy) ((bounds (neg_parameter hy)).2.2.2.trans
      (by simpa only [abs_of_neg (lt_of_not_ge hp)] using hx))

theorem continuous (y : ℝ) (hy : y ∈ Set.Icc (-1) 1) :
    Continuous (fun x : ℝ => F x y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hp : 0 < vartheta⁻¹ := inv_pos.mpr (by linarith [vartheta_spec.1])
    have he : (fun x : ℝ => F x y) =ᶠ[𝓝 0] (fun _ => 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hp] with x h
      apply near_zero hy
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using h)
    exact continuousAt_const.congr_of_eventuallyEq he
  · have he : (fun x : ℝ => F x y) =ᶠ[𝓝 x]
        (fun x => max (min (x ^ 2 + x * y + 1) |x|⁻¹ -
          max (x ^ 2 + x * y - 1) (-|x|⁻¹)) 0) := by
      filter_upwards [eventually_ne_nhds hx] with z hz
      exact length_formula hz y
    have hc : ContinuousAt (fun x : ℝ => max (min (x ^ 2 + x * y + 1) |x|⁻¹ -
          max (x ^ 2 + x * y - 1) (-|x|⁻¹)) 0) x := by
      fun_prop (disch := exact abs_ne_zero.mpr hx)
    exact hc.congr_of_eventuallyEq he

theorem intervalIntegrable {y a b : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    IntervalIntegrable (fun x => F x y) volume a b :=
  (continuous y hy).intervalIntegrable _ _

theorem integral_compact {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    g y = ∫ x in -vartheta..vartheta, F x y := by
  have hp : 0 ≤ vartheta := by linarith [vartheta_spec.1]
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    apply outside hy
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact (neg_le_abs x).trans' (by linarith)
    · exact (le_abs_self x).trans' hx.le)).symm

end Cubic.AllGaloisCounts.SlicePieces
