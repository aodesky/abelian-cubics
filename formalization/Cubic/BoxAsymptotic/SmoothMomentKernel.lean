import Cubic.BoxAsymptotic.SmoothTransformBounds
import Cubic.BoxAsymptotic.AngularMomentSums

/-! Absorbing the moment logarithm into a fixed transform decay. The scale
`D` will be `2X+Θ⁻¹`; no power of `Θ⁻¹` is lost in this estimate. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothMomentKernel

theorem polynomial_decay {u : ℝ} {N j : ℕ} (hu : 1 ≤ u) (hj : N + 2 ≤ j) :
    u ^ N / u ^ j ≤ 1 / u ^ 2 := by
  calc
    _ ≤ u ^ N / u ^ (N + 2) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (pow_le_pow_right₀ hu hj)
    _ = _ := by rw [pow_add]; field_simp

theorem log_bound {K Θ D t : ℝ} (hK : 2 ≤ K) (hΘ : 0 < Θ)
    (hD : 1 ≤ D) (hDΘ : 1 ≤ D * Θ) (hL : 1 ≤ Real.log (2 * D)) :
    Real.log (2 * K + 2 * |t|) ≤
      Real.log (2 * D) * (1 + K * Θ) * (1 + |t|) := by
  have hu : 0 ≤ K * Θ := mul_nonneg (by linarith) hΘ.le
  have hDK : K ≤ D * (1 + K * Θ) := by
    have h := mul_le_mul_of_nonneg_right hDΘ (show 0 ≤ K by linarith)
    nlinarith
  have hD1 : 1 ≤ D * (1 + K * Θ) := by nlinarith
  have hm : 2 * K + 2 * |t| ≤ (2 * D) * (1 + K * Θ) * (1 + |t|) := by
    have h := mul_le_mul_of_nonneg_right hD1 (abs_nonneg t)
    nlinarith
  have hlu := Real.log_le_sub_one_of_pos (show 0 < 1 + K * Θ by positivity)
  have hlv := Real.log_le_sub_one_of_pos (show 0 < 1 + |t| by positivity)
  calc
    _ ≤ Real.log ((2 * D) * (1 + K * Θ) * (1 + |t|)) :=
      Real.log_le_log (by linarith [abs_nonneg t]) hm
    _ = Real.log (2 * D) + Real.log (1 + K * Θ) + Real.log (1 + |t|) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    _ ≤ Real.log (2 * D) + K * Θ + |t| := by linarith
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hL hu
      have h2 := mul_le_mul_of_nonneg_right hL (abs_nonneg t)
      have h3 : 0 ≤ Real.log (2 * D) * (K * Θ) * |t| := by positivity
      nlinarith

theorem decay {K Θ D t : ℝ} {A j : ℕ} (hK : 2 ≤ K) (hΘ : 0 < Θ)
    (hD : 1 ≤ D) (hDΘ : 1 ≤ D * Θ) (hL : 1 ≤ Real.log (2 * D))
    (hj : 2 * A + 2 ≤ j) :
    (1 + |t|) ^ A * Real.log (2 * K + 2 * |t|) ^ A /
        ((1 + K * Θ) ^ j * (1 + |t|) ^ j) ≤
      Real.log (2 * D) ^ A / ((1 + K * Θ) ^ 2 * (1 + |t|) ^ 2) := by
  have hu : 1 ≤ 1 + K * Θ := by nlinarith
  have hv : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hl0 : 0 ≤ Real.log (2 * K + 2 * |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hp := pow_le_pow_left₀ hl0 (log_bound hK hΘ hD hDΘ hL) A
  have hnum : (1 + |t|) ^ A * Real.log (2 * K + 2 * |t|) ^ A ≤
      Real.log (2 * D) ^ A * (1 + K * Θ) ^ A * (1 + |t|) ^ (2 * A) := by
    convert mul_le_mul_of_nonneg_left hp (show 0 ≤ (1 + |t|) ^ A by positivity) using 1
    rw [mul_pow, mul_pow, show 2 * A = A + A by omega, pow_add]
    ring
  calc
    _ ≤ (Real.log (2 * D) ^ A * (1 + K * Θ) ^ A * (1 + |t|) ^ (2 * A)) /
        ((1 + K * Θ) ^ j * (1 + |t|) ^ j) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (Real.log (2 * D) ^ A * (1 + K * Θ) ^ A * (1 + |t|) ^ (2 * A)) /
        ((1 + K * Θ) ^ (A + 2) * (1 + |t|) ^ (2 * A + 2)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul (pow_le_pow_right₀ hu (by omega)) (pow_le_pow_right₀ hv hj)
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; field_simp

end Cubic.BoxAsymptotic.SmoothMomentKernel
