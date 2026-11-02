import Cubic.AllGaloisCounts.SlicePieces
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Integration in the root variable: the actual slice integral equals the
two moving-endpoint integrals in the manuscript. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SlicePrimitive
open CountData LinearFactorSlice SliceThresholds SliceRegularity SlicePieces MeasureTheory

def primitive (x y : ℝ) : ℝ := x + Real.log x - x ^ 3 / 3 - y * x ^ 2 / 2

theorem primitive_deriv {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun x => primitive x y) (psi x y) x := by
  convert (((hasDerivAt_id x).add (Real.hasDerivAt_log hx.ne')).sub
    ((hasDerivAt_pow 3 x).div_const 3)).sub
      (((hasDerivAt_pow 2 x).const_mul y).div_const 2) using 1 <;>
    simp only [primitive, psi] <;> ring

theorem integral_psi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    (∫ x in a..b, psi x y) = primitive b y - primitive a y := by
  have hc : ContinuousOn (fun x => psi x y) (Set.Icc a b) := by
    intro x hx
    exact (psi_deriv (ha.trans_le hx.1) y).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact primitive_deriv (ha.trans_le hx.1) y
  · exact hc.intervalIntegrable_of_Icc hab

def h (y : ℝ) : ℝ := 2 * minus y + primitive (plus y) y - primitive (minus y) y

theorem h_eq {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    h y = 2 * minus y + ∫ x in minus y..plus y, psi x y := by
  rw [integral_psi (a := minus y)
    (crossing_pos (parameter_domain hy) (by norm_num)) (order hy).le y]
  unfold h
  ring

theorem positive_integral {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    (∫ x in 0..vartheta, F x y) = h y := by
  have hm : 0 < minus y := crossing_pos (parameter_domain hy) (by norm_num)
  have hp : plus y ≤ vartheta := (bounds hy).2.2.2
  have hmp := (order hy).le
  have hfirst : (∫ x in 0..minus y, F x y) = 2 * minus y := by
    calc _ = ∫ _ : ℝ in 0..minus y, (2 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hm.le]
          intro x hx
          exact before hy hx.1 hx.2
      _ = _ := by simp; ring
  have hmid : (∫ x in minus y..plus y, F x y) =
      ∫ x in minus y..plus y, psi x y := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hmp]
    intro x hx
    exact middle hy hx.1 hx.2
  have hlast : (∫ x in plus y..vartheta, F x y) = 0 := by
    calc _ = ∫ _ : ℝ in plus y..vartheta, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hp]
          intro x hx
          exact after hy hx.1
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable hy (a := 0) (b := minus y)) (intervalIntegrable hy (b := vartheta)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable hy (a := minus y) (b := plus y)) (intervalIntegrable hy (b := vartheta)),
    hfirst, hmid, hlast, add_zero, h_eq hy]

theorem g_eq {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) : g y = h y + h (-y) := by
  rw [integral_compact hy, ← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable hy (a := -vartheta) (b := 0)) (intervalIntegrable hy (b := vartheta)),
    positive_integral hy]
  have hn : (∫ x in -vartheta..0, F x y) = h (-y) := by
    calc _ = ∫ x in (0 : ℝ)..vartheta, F (-x) y := by
          simpa using (intervalIntegral.integral_comp_neg
            (f := fun x => F x y) (a := 0) (b := vartheta)).symm
      _ = ∫ x in (0 : ℝ)..vartheta, F x (-y) := by simp only [reflect]
      _ = _ := positive_integral (neg_parameter hy)
  rw [hn, add_comm]

theorem h_contDiffAt {y : ℝ} (hy : y ∈ Set.Ioo (-2) 2) : ContDiffAt ℝ 2 h y := by
  have hm : ContDiffAt ℝ 2 minus y := crossing_contDiffAt hy (by norm_num)
  have hp : ContDiffAt ℝ 2 plus y := crossing_contDiffAt hy (by norm_num)
  have hm0 : minus y ≠ 0 := (crossing_pos hy (by norm_num : (2 : ℝ) ∈ Set.Icc 0 2)).ne'
  have hp0 : plus y ≠ 0 := (crossing_pos hy (by norm_num : (0 : ℝ) ∈ Set.Icc 0 2)).ne'
  have hmP : ContDiffAt ℝ 2 (fun z => primitive (minus z) z) y := by
    exact ((hm.add (hm.log hm0)).sub ((hm.pow 3).div_const 3)).sub
      ((contDiffAt_id.mul (hm.pow 2)).div_const 2)
  have hpP : ContDiffAt ℝ 2 (fun z => primitive (plus z) z) y := by
    exact ((hp.add (hp.log hp0)).sub ((hp.pow 3).div_const 3)).sub
      ((contDiffAt_id.mul (hp.pow 2)).div_const 2)
  exact ((contDiffAt_const.mul hm).add hpP).sub hmP

theorem g_contDiffOn : ContDiffOn ℝ 2 g (Set.Icc (-1) 1) := by
  have hc : ContDiffOn ℝ 2 (fun y => h y + h (-y)) (Set.Icc (-1) 1) := by
    intro y hy
    exact ((h_contDiffAt (parameter_domain hy)).add
      ((h_contDiffAt (parameter_domain (neg_parameter hy))).comp y
        contDiffAt_id.neg)).contDiffWithinAt
  exact hc.congr (fun y hy => g_eq hy)

theorem boundary : g 1 = markedBoundary := by
  rw [g_eq (by norm_num), h, h, endpoints.1, endpoints.2.1,
    endpoints.2.2.1, endpoints.2.2.2]
  simp only [primitive, Real.log_one, Real.log_inv, one_pow, neg_mul, one_mul]
  unfold markedBoundary
  rw [theta_inverse_cube]
  have ht := vartheta_spec.2.2
  have hs := theta_inverse_square
  have hi := theta_inverse
  rw [div_eq_mul_inv (2 : ℝ) (3 * vartheta), mul_inv_rev]
  nlinarith

end Cubic.AllGaloisCounts.SlicePrimitive
