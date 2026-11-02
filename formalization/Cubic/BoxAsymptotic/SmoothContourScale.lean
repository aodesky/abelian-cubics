import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Choosing the contour distance `η = 1/(4 log D)` with `D = 2X+Θ⁻¹`.
This turns the loss `η⁻⁴` into four logarithms and keeps `X^η` bounded. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothContourScale

theorem scale_conditions {X Θ : ℝ} (hX : 2 ≤ X) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1) :
    let D := 2 * X + Θ⁻¹
    1 ≤ D ∧ 1 ≤ D * Θ ∧ 1 ≤ Real.log D ∧ 1 ≤ Real.log (2 * D) ∧ X ≤ D := by
  dsimp only
  have hi : 1 ≤ Θ⁻¹ := (one_le_inv₀ hΘ).mpr hΘ'
  have hD : 5 ≤ 2 * X + Θ⁻¹ := by linarith
  have hprod : 1 ≤ (2 * X + Θ⁻¹) * Θ := by
    rw [add_mul, inv_mul_cancel₀ hΘ.ne']
    nlinarith
  have hlog : 1 ≤ Real.log (2 * X + Θ⁻¹) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by have := Real.exp_one_lt_d9; linarith)
  refine ⟨by linarith, hprod, hlog, hlog.trans ?_, by linarith⟩
  exact Real.log_le_log (by linarith) (by linarith)

theorem eta_conditions {D : ℝ} (hL : 1 ≤ Real.log D) :
    0 < (4 * Real.log D)⁻¹ ∧ (4 * Real.log D)⁻¹ ≤ 1 / 4 := by
  refine ⟨by positivity, ?_⟩
  rw [← one_div, div_le_div_iff₀ (by positivity : 0 < 4 * Real.log D) (by norm_num : (0 : ℝ) < 4)]
  linarith

theorem radial_bound {X D : ℝ} (hX : 0 < X) (hXD : X ≤ D)
    (hL : 1 ≤ Real.log D) :
    X ^ (1 / 2 + (4 * Real.log D)⁻¹) ≤ Real.exp 1 * Real.sqrt X := by
  have hη : 0 < (4 * Real.log D)⁻¹ := by positivity
  have hp : Real.log X * (4 * Real.log D)⁻¹ ≤ 1 := by
    calc
      _ ≤ Real.log D * (4 * Real.log D)⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.log_le_log hX hXD) hη.le
      _ = 1 / 4 := by field_simp
      _ ≤ 1 := by norm_num
  rw [Real.rpow_add hX, ← Real.sqrt_eq_rpow]
  have he : X ^ (4 * Real.log D)⁻¹ ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hX]
    exact Real.exp_le_exp.mpr hp
  exact (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg X)).trans_eq (mul_comm _ _)

theorem logarithmic_bound {D : ℝ} (hD : 2 ≤ D) (hL : 1 ≤ Real.log D) (A : ℕ) :
    ((4 * Real.log D)⁻¹)⁻¹ ^ 4 * Real.log (2 * D) ^ A ≤
      (4 : ℝ) ^ 4 * 2 ^ A * Real.log D ^ (A + 4) := by
  have hl : Real.log (2 * D) ≤ 2 * Real.log D := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hD
    linarith
  have h0 : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
  calc
    _ ≤ (4 * Real.log D) ^ 4 * (2 * Real.log D) ^ A := by
      rw [inv_inv]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hl A) (by positivity)
    _ = _ := by rw [mul_pow, mul_pow, pow_add]; ring

end Cubic.BoxAsymptotic.SmoothContourScale
