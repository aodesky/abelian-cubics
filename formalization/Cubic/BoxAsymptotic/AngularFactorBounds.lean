import Cubic.BoxAsymptotic.AngularLocalSeries

/-! The factor at three is uniformly bounded on `Re s ≥ 1/2`, as used in
`lem:moment`. This estimates the independently defined local factor; it does
not assume continuation of the original Dirichlet series to this half-plane. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularFactorBounds

open Cubic.BoxAsymptotic.AngularLocalSeries
open Cubic.BoxAsymptotic.AngularLocalData Cubic.BoxAsymptotic.AngularRamified

theorem norm_y_le (k : ℤ) (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) : ‖y k s‖ ≤ 2 / 3 := by
  have hsq : ‖y k s‖ ^ 2 ≤ (1 / 3 : ℝ) := by
    calc
      ‖y k s‖ ^ 2 = (3 : ℝ) ^ (-s.re * 2) := by
        rw [y, norm_mul, norm_ramifiedPhase, one_mul,
          show (3 : ℂ) = ((3 : ℝ) : ℂ) by rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re,
          Real.rpow_mul (by norm_num), Real.rpow_two]
      _ ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 3 := by norm_num
  nlinarith [norm_nonneg (y k s)]

/-- An absolute bound sufficient for the first-moment estimate. -/
theorem localFactor_bound (k : ℤ) (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖localFactor k s‖ ≤ 2 := by
  have hy := norm_y_le k s hs
  have hd : (1 / 3 : ℝ) ≤ ‖1 - y k s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (y k s)
    norm_num only [norm_one] at h
    linarith
  have hq : ‖y k s ^ 2 / (1 - y k s)‖ ≤ (4 / 3 : ℝ) := by
    rw [norm_div, norm_pow]
    apply (div_le_iff₀ (by linarith : 0 < ‖1 - y k s‖)).mpr
    nlinarith [norm_nonneg (y k s)]
  by_cases hk : 6 ∣ k
  · have ht : ‖3 * y k s ^ 2 / (1 - y k s)‖ ≤ (4 : ℝ) := by
      rw [mul_div_assoc, norm_mul]
      norm_num only [Complex.norm_ofNat]
      linarith
    have h := norm_add_le (1 + y k s) (3 * y k s ^ 2 / (1 - y k s))
    have h' := norm_add_le (1 : ℂ) (y k s)
    simp only [norm_one] at h'
    simp only [localFactor, hk, ite_true, mul_one, norm_mul, norm_div, norm_one]
    norm_num
    linarith
  · have h := norm_add_le (1 : ℂ) (y k s)
    simp only [norm_one] at h
    simp only [localFactor, hk, ite_false, mul_zero, zero_mul, zero_div, add_zero,
      norm_mul, norm_div, norm_one]
    norm_num
    linarith

end Cubic.BoxAsymptotic.AngularFactorBounds
