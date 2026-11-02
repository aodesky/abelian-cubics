import Cubic.BoxAsymptotic.AngularMomentDyadic

/-! Elementary scale comparisons in the dyadic second-moment argument.
These estimates retain a fixed logarithmic power and do not introduce a
power of the frequency parameter. -/

namespace Cubic.BoxAsymptotic.DyadicSieveScale

theorem log_two_mul_ge_one {Y : ℝ} (hY : 2 ≤ Y) : 1 ≤ Real.log (2 * Y) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ 2 * Y)
  rw [h4] at hm
  norm_num at h2
  linarith

theorem dyadic_log {Y : ℝ} (hY : 1 ≤ Y) (j : ℕ) :
    Real.log (2 * ((2 : ℝ) ^ j * Y)) ≤ ((j : ℝ) + 1) * Real.log (2 * Y) := by
  have hY0 : 0 < Y := by linarith
  have he : 2 * ((2 : ℝ) ^ j * Y) = (2 : ℝ) ^ j * (2 * Y) := by ring
  rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j)]

theorem dyadic_sieve_scale {K Y : ℝ} (hKY : K ≤ 2 * Y)
    (hY : 2 ≤ Y) (j : ℕ) :
    (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5 ≤
      3 * (4 : ℝ) ^ j * ((j : ℝ) + 1) ^ 6 * Y * Real.log (2 * Y) ^ 6 := by
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hfour : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hY0 : 0 ≤ Y := by linarith
  have hscale : K + (2 : ℝ) ^ j * Y ≤ 3 * (4 : ℝ) ^ j * Y := by
    nlinarith [mul_le_mul_of_nonneg_right hfour hY0,
      mul_le_mul_of_nonneg_right htwo hY0]
  have hl1 := log_two_mul_ge_one hY
  have hlog0 : 0 ≤ Real.log (2 * ((2 : ℝ) ^ j * Y)) :=
    Real.log_nonneg (by nlinarith [mul_le_mul_of_nonneg_right htwo hY0])
  have hlog := pow_le_pow_left₀ hlog0 (dyadic_log (by linarith) j) 5
  have hp : (((j : ℝ) + 1) * Real.log (2 * Y)) ^ 5 ≤
      (((j : ℝ) + 1) * Real.log (2 * Y)) ^ 6 := by
    exact pow_le_pow_right₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)
  calc
    _ ≤ (3 * (4 : ℝ) ^ j * Y) * ((((j : ℝ) + 1) * Real.log (2 * Y)) ^ 6) :=
      mul_le_mul hscale (hlog.trans hp) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The growth allowed by the dual coefficients is absorbed by the cubic
weight decay and the sieve scale, leaving a summable geometric sequence. -/
theorem combine_decay (j : ℕ) :
    ((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 *
      (3 * (4 : ℝ) ^ j * ((j : ℝ) + 1) ^ 6) =
      3 * Cubic.BoxAsymptotic.AngularMomentDyadic.weight j ^ 2 := by
  have he : ((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 * (4 : ℝ) ^ j = (1 / 2 : ℝ) ^ (j * 2) := by
    rw [← mul_pow, ← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
    norm_num
    rw [pow_mul]
    norm_num
  calc
    _ = 3 * (((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 * (4 : ℝ) ^ j) * ((j : ℝ) + 1) ^ 6 := by ring
    _ = 3 * (1 / 2 : ℝ) ^ (j * 2) * ((j : ℝ) + 1) ^ 6 := by rw [he]
    _ = _ := by
      rw [Cubic.BoxAsymptotic.AngularMomentDyadic.weight, mul_pow, ← pow_mul, ← pow_mul]
      norm_num
      ring

end Cubic.BoxAsymptotic.DyadicSieveScale
