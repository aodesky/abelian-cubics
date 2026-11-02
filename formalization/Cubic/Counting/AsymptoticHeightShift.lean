import Cubic.Counting.AsymptoticConstantScaling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The `+1` in the height change does not alter either main coefficient

The paper substitutes `X=3H²+1`. We check that replacing this by `3H²` in
the main term has error `O(log H)`. This estimate is independent of the coefficient-counting asymptotic (`eqn:dSummatoryForGeneralTrace`).
-/

noncomputable section

namespace Cubic.Counting.AsymptoticHeightShift

open Filter Asymptotics AsymptoticConstantScaling

theorem xlog_increment (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (x + 1) * Real.log (x + 1) - x * Real.log x ∧
      (x + 1) * Real.log (x + 1) - x * Real.log x ≤ Real.log (x + 1) + 1 := by
  have hx0 : 0 < x := by linarith
  have hmono := Real.log_le_log hx0 (show x ≤ x + 1 by linarith)
  have hlog : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div (by positivity) hx0.ne']
    congr 1
    field_simp
  have hlo : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hu := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity)
  have hmul := mul_le_mul_of_nonneg_left hu hx0.le
  have hcancel : x * (1 + 1 / x - 1) = 1 := by field_simp; ring
  rw [hcancel, ← hlog] at hmul
  constructor
  · nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hmono)]
  · nlinarith

theorem height_log_increment_bound (H : ℝ) (hH : 1 ≤ H) (hl : 1 ≤ Real.log H) :
    ‖(((3 * H ^ 2 + 1) * Real.log (3 * H ^ 2 + 1) -
      (3 * H ^ 2) * Real.log (3 * H ^ 2) : ℝ) : ℂ)‖ ≤ 6 * Real.log H := by
  have hH0 : 0 < H := by linarith
  have hsq : 1 ≤ H ^ 2 := by nlinarith
  have hi := xlog_increment (3 * H ^ 2) (by nlinarith)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi.1]
  have hlog := Real.log_le_log (show 0 < 3 * H ^ 2 + 1 by positivity)
    (show 3 * H ^ 2 + 1 ≤ 4 * H ^ 2 by nlinarith)
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hH0.ne'), Real.log_pow] at hlog
  have hfour : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- Both constants in the final theorem survive the exact `X=3H²+1` substitution. -/
theorem main_term_height_shift (c₂ c₁ : ℂ) :
    (fun H : ℝ => toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2 + 1) -
      rootPolynomialMainTerm c₂ c₁ H) =O[atTop] (fun H : ℝ => Real.log H) := by
  let A : ℂ := c₂ / 8
  let B : ℂ := c₁ / 4 - c₂ / 8 - (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ))
  apply IsBigO.of_bound (6 * ‖A‖ + ‖B‖)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with H hH hl
  have hH0 : 0 < H := by linarith
  rw [← height_rescaling c₂ c₁ H hH0]
  have he : toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2 + 1) -
      toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2) =
      A * (((3 * H ^ 2 + 1) * Real.log (3 * H ^ 2 + 1) -
        (3 * H ^ 2) * Real.log (3 * H ^ 2) : ℝ) : ℂ) + B := by
    dsimp [toricPolynomialMainTerm, A, B]
    push_cast
    ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log H)]
  calc
    _ ≤ ‖A‖ * ‖(((3 * H ^ 2 + 1) * Real.log (3 * H ^ 2 + 1) -
        (3 * H ^ 2) * Real.log (3 * H ^ 2) : ℝ) : ℂ)‖ + ‖B‖ := by
      simpa only [norm_mul] using norm_add_le (A * _) B
    _ ≤ ‖A‖ * (6 * Real.log H) + ‖B‖ := by
      gcongr
      exact height_log_increment_bound H hH hl
    _ ≤ (6 * ‖A‖ + ‖B‖) * Real.log H := by
      nlinarith [norm_nonneg B]

end Cubic.Counting.AsymptoticHeightShift
