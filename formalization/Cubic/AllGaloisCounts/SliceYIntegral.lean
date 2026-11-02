import Cubic.AllGaloisCounts.SlicePieces

/-! The rectangular and triangular areas obtained by integrating the
clipped affine function in the coefficient variable first. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceYIntegral
open CountData LinearFactorSlice SliceThresholds SlicePieces MeasureTheory

def J (x : ℝ) : ℝ := ∫ y in (-1 : ℝ)..1, F x y

theorem continuous_y (x : ℝ) : Continuous (fun y : ℝ => F x y) := by
  by_cases hx : x = 0
  · simp only [hx, F, if_pos rfl]
    exact continuous_const
  · simp only [length_formula hx]
    fun_prop

theorem psi_level_le {x y t : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (ht : t ∈ Set.Icc 0 2) (hx : 0 < x) (hxc : x ≤ crossing t y) :
    t ≤ psi x y := by
  have h := (strictAnti_psi (parameter_domain hy).1).antitoneOn
    hx (crossing_pos (parameter_domain hy) ht) hxc
  change psi (crossing t y) y ≤ psi x y at h
  simpa only [(crossing_spec (parameter_domain hy) ht).2] using h

theorem psi_le_level {x y t : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    (ht : t ∈ Set.Icc 0 2) (hxc : crossing t y ≤ x) : psi x y ≤ t := by
  have hp := crossing_pos (parameter_domain hy) ht
  have h := (strictAnti_psi (parameter_domain hy).1).antitoneOn hp
    (hp.trans_le hxc) hxc
  change psi x y ≤ psi (crossing t y) y at h
  simpa only [(crossing_spec (parameter_domain hy) ht).2] using h

theorem integral_psi_y (x a b : ℝ) :
    (∫ y in a..b, psi x y) =
      (b - a) * (1 + x⁻¹ - x ^ 2) - x * (b ^ 2 - a ^ 2) / 2 := by
  have hd (y : ℝ) : HasDerivAt
      (fun y => y * (1 + x⁻¹ - x ^ 2) - x * y ^ 2 / 2) (psi x y) y := by
    convert ((hasDerivAt_id y).mul_const _).sub
      (((hasDerivAt_pow 2 y).const_mul x).div_const 2) using 1 <;>
      simp only [psi] <;> ring
  have hi : IntervalIntegrable (fun y => psi x y) volume a b :=
    (show Continuous (fun y => psi x y) by unfold psi; fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hi]
  ring

theorem rectangle {x : ℝ} (hx : 0 ≤ x) (hxt : x ≤ vartheta⁻¹) : J x = 4 := by
  calc _ = ∫ _ : ℝ in (-1 : ℝ)..1, (2 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        intro y hy
        exact before hy hx (hxt.trans (bounds hy).1)
    _ = _ := by norm_num

theorem upper_triangle {x : ℝ} (hxt : vartheta⁻¹ ≤ x) (hx1 : x ≤ 1) :
    J x = 4 - x / 2 * (1 + x + x⁻¹ - (x ^ 2)⁻¹) ^ 2 := by
  have hx : 0 < x := (inv_pos.mpr (by linarith [vartheta_spec.1])).trans_le hxt
  have hlow : 2 ≤ psi x (-1) := psi_level_le (by norm_num) (by norm_num) hx
    (show x ≤ minus (-1) by rw [endpoints.2.2.1]; exact hx1)
  have hhigh : psi x 1 ≤ 2 := psi_le_level (by norm_num) (by norm_num)
    (show minus 1 ≤ x by rw [endpoints.1]; exact hxt)
  have hzero : 0 ≤ psi x 1 := psi_level_le (by norm_num) (by norm_num) hx
    (show x ≤ plus 1 by rw [endpoints.2.1]; exact hx1)
  let q := (1 + x⁻¹ - x ^ 2 - 2) / x
  have he : psi x q = 2 := by dsimp [psi, q]; field_simp; ring
  have hq : q ∈ Set.Icc (-1) 1 := by
    dsimp [psi] at hlow hhigh he
    constructor <;> nlinarith
  have hleft : (∫ y in (-1 : ℝ)..q, F x y) = 2 * (q + 1) := by
    calc _ = ∫ _ : ℝ in (-1 : ℝ)..q, (2 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hq.1]
          intro y hy
          have hc : 2 ≤ psi x y := by
            dsimp [psi] at he ⊢
            nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy.2)]
          rw [clipped hx hy.1, max_eq_right (by linarith), min_eq_left hc]
      _ = _ := by simp; ring
  have hright : (∫ y in q..1, F x y) = ∫ y in q..1, psi x y := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hq.2]
    intro y hy
    have hge : 0 ≤ psi x y := by
      dsimp [psi] at hzero ⊢
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy.2)]
    have hle : psi x y ≤ 2 := by
      dsimp [psi] at he ⊢
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy.1)]
    rw [clipped hx (hq.1.trans hy.1), max_eq_right hge, min_eq_right hle]
  unfold J
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_y x).intervalIntegrable (-1) q) ((continuous_y x).intervalIntegrable q 1),
    hleft, hright, integral_psi_y]
  dsimp [q]
  field_simp
  <;> ring

theorem lower_triangle {x : ℝ} (hx1 : 1 ≤ x) (hxt : x ≤ vartheta) :
    J x = x / 2 * (1 - x + x⁻¹ + (x ^ 2)⁻¹) ^ 2 := by
  have hx : 0 < x := by linarith
  have hlow : psi x (-1) ≤ 2 := psi_le_level (by norm_num) (by norm_num)
    (show minus (-1) ≤ x by rw [endpoints.2.2.1]; exact hx1)
  have hhigh : psi x 1 ≤ 0 := psi_le_level (by norm_num) (by norm_num)
    (show plus 1 ≤ x by rw [endpoints.2.1]; exact hx1)
  have hzero : 0 ≤ psi x (-1) := psi_level_le (by norm_num) (by norm_num) hx
    (show x ≤ plus (-1) by rw [endpoints.2.2.2]; exact hxt)
  let q := (1 + x⁻¹ - x ^ 2) / x
  have he : psi x q = 0 := by dsimp [psi, q]; field_simp; ring
  have hq : q ∈ Set.Icc (-1) 1 := by
    dsimp [psi] at hzero hhigh he
    constructor <;> nlinarith
  have hleft : (∫ y in (-1 : ℝ)..q, F x y) = ∫ y in (-1 : ℝ)..q, psi x y := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hq.1]
    intro y hy
    have hge : 0 ≤ psi x y := by
      dsimp [psi] at he ⊢
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy.2)]
    have hle : psi x y ≤ 2 := by
      dsimp [psi] at hlow ⊢
      nlinarith [mul_nonneg hx.le (by linarith [hy.1] : 0 ≤ y + 1)]
    rw [clipped hx hy.1, max_eq_right hge, min_eq_right hle]
  have hright : (∫ y in q..1, F x y) = 0 := by
    calc _ = ∫ _ : ℝ in q..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hq.2]
          intro y hy
          have hc : psi x y ≤ 0 := by
            dsimp [psi] at he ⊢
            nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy.1)]
          rw [clipped hx (hq.1.trans hy.1), max_eq_left hc]
          norm_num
      _ = _ := by simp
  unfold J
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_y x).intervalIntegrable (-1) q) ((continuous_y x).intervalIntegrable q 1),
    hleft, hright, add_zero, integral_psi_y]
  dsimp [q]
  field_simp
  <;> ring

theorem zero {x : ℝ} (hx : vartheta ≤ x) : J x = 0 := by
  calc _ = ∫ _ : ℝ in (-1 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        intro y hy
        exact after hy ((bounds hy).2.2.2.trans hx)
    _ = _ := by simp

end Cubic.AllGaloisCounts.SliceYIntegral
