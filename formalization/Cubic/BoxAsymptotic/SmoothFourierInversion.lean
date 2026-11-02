import Cubic.BoxAsymptotic.SmoothAngularTransform
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

/-! Fourier reconstruction for the actual angular coefficients. Two bounded
angular derivatives imply absolute convergence; the reconstruction theorem is
mathlib's Fourier theorem on the circle of period `2π`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothFourierInversion

open MeasureTheory Complex Set
open Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothAngularTransform
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

theorem character_eq_fourier (k : ℤ) (θ : ℝ) :
    character k θ = fourier k (θ : AddCircle (2 * Real.pi)) := by
  rw [character_eq_exp, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem coefficient_bound {w : ℝ × ℝ → ℝ} {M : ℝ}
    (hb : ∀ p, |w p| ≤ M) (k : ℤ) (x : ℝ) :
    ‖angularCoefficient w k x‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := fun θ => (w (x, θ) : ℂ) * character (-k) θ)
    (C := M) (fun θ _ => by simpa only [norm_mul, norm_character,
      mul_one, Complex.norm_real, Real.norm_eq_abs] using hb (x, θ))
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
  unfold angularCoefficient
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = M := by field_simp

theorem coefficient_summable {w : ℝ × ℝ → ℝ} {Θ M : ℝ}
    (hw : ContDiff ℝ ∞ w) (hΘ : 0 < Θ)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hb : normalizedDerivativeBound w Θ M 2) (x : ℝ) :
    Summable (fun k : ℤ => angularCoefficient w k x) := by
  have hmajor : Summable (fun k : ℤ => (M / Θ ^ 2) * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [show ∀ᶠ k : ℤ in Filter.cofinite, k ≠ 0 from
    (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have h := coefficient_bound (hb 0 2 (by omega)) k x
  simp only [Function.iterate_zero, id_eq] at h
  rw [coefficient_angular_iterate hw hp, norm_mul, norm_pow, norm_mul,
    norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hΘ, Complex.norm_intCast, mul_pow, sq_abs] at h
  calc
    _ ≤ M / (Θ ^ 2 * (k : ℝ) ^ 2) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h)
    _ = _ := by field_simp

theorem reconstruction {w : ℝ × ℝ → ℝ}
    (hw : Continuous w)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (x θ : ℝ) (hs : Summable (fun k : ℤ => angularCoefficient w k x)) :
    HasSum (fun k : ℤ => angularCoefficient w k x * character k θ) (w (x, θ) : ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let f : ℝ → ℂ := fun u => (w (x, u) : ℂ)
  have hfc : Continuous f := Complex.continuous_ofReal.comp
    (hw.comp (continuous_const.prodMk continuous_id))
  have hfp : Function.Periodic f (2 * Real.pi) := fun u => by
    dsimp [f]
    rw [hp]
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨hfp.lift, continuous_coinduced_dom.mpr hfc⟩
  have hc (k : ℤ) : fourierCoeff F k = angularCoefficient w k x := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, F, ContinuousMap.coe_mk, Function.Periodic.lift_coe,
      smul_eq_mul, ← character_eq_fourier, angularCoefficient, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
      one_div]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    exact mul_comm _ _
  have h := has_pointwise_sum_fourier_series_of_summable
    (show Summable (fourierCoeff F) by
      convert hs using 1
      exact funext hc)
    (θ : AddCircle (2 * Real.pi))
  simp only [hc, smul_eq_mul, ← character_eq_fourier] at h
  simpa only [F,
    ContinuousMap.coe_mk, Function.Periodic.lift_coe, f] using h

end Cubic.BoxAsymptotic.SmoothFourierInversion
