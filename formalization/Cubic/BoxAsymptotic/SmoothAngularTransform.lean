import Cubic.BoxAsymptotic.SmoothTransformData
import Cubic.BoxAsymptotic.SmoothWeightCalculus
import Cubic.Analysis.CompactParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Angular integration by parts for the test weight, retaining the paper's
positive Fourier sign for the arithmetic series. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothAngularTransform

open Complex MeasureTheory Set
open Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.BoxAsymptotic.SmoothWeightCalculus
open scoped ContDiff

theorem character_hasDerivAt (k : ℤ) (θ : ℝ) :
    HasDerivAt (character k) ((k : ℂ) * I * character k θ) θ := by
  have h := (((hasDerivAt_id θ).ofReal_comp.const_mul (k : ℂ)).mul_const I).cexp
  convert h using 1
  · ext y
    exact character_eq_exp k y
  · simp only [id_eq, Complex.ofReal_one, mul_one, character_eq_exp]
    ring

theorem character_at_period (k : ℤ) : character k (2 * Real.pi) = 1 := by
  simp [character, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]

theorem coefficient_angularDerivative {w : ℝ × ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ)) (Θ : ℝ) (k : ℤ) (x : ℝ) :
    angularCoefficient (angularDerivative Θ w) k x =
      ((Θ : ℂ) * (k : ℂ) * I) * angularCoefficient w k x := by
  let f : ℝ → ℝ := fun θ => w (x, θ)
  have hf : ContDiff ℝ ∞ f := hw.comp (contDiff_const.prodMk contDiff_id)
  have hd (θ : ℝ) : HasDerivAt (fun u => (f u : ℂ)) ((deriv f θ : ℝ) : ℂ) θ :=
    ((hf.differentiable (by simp) θ).hasDerivAt).ofReal_comp
  have hdf : Continuous (fun θ => ((deriv f θ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hf.continuous_deriv (by simp))
  have hchar : Continuous (fun θ => ((-k : ℤ) : ℂ) * I * character (-k) θ) :=
    continuous_const.mul (continuous_character _)
  have h := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun θ _ => hd θ)
    (fun θ _ => character_hasDerivAt (-k) θ)
    (hdf.intervalIntegrable _ _) (hchar.intervalIntegrable _ _)
  have hfi : IntervalIntegrable (fun θ => ((deriv f θ : ℝ) : ℂ) * character (-k) θ)
      volume 0 (2 * Real.pi) := (hdf.mul (continuous_character _)).intervalIntegrable _ _
  have hgi : IntervalIntegrable
      (fun θ => (f θ : ℂ) * (((-k : ℤ) : ℂ) * I * character (-k) θ))
      volume 0 (2 * Real.pi) :=
    ((Complex.continuous_ofReal.comp hf.continuous).mul hchar).intervalIntegrable _ _
  have hperiod : f (2 * Real.pi) = f 0 := by simpa [f] using hp x 0
  rw [intervalIntegral.integral_add hfi hgi, character_at_period] at h
  simp only [character, ofReal_zero, zero_mul, Complex.exp_zero, one_zpow, mul_one,
    hperiod, sub_self] at h
  have he : (∫ θ in (0 : ℝ)..2 * Real.pi, ((deriv f θ : ℝ) : ℂ) * character (-k) θ) =
      (k : ℂ) * I * (∫ θ in (0 : ℝ)..2 * Real.pi, (f θ : ℂ) * character (-k) θ) := by
    have hh : (∫ θ in (0 : ℝ)..2 * Real.pi,
        (f θ : ℂ) * (((-k : ℤ) : ℂ) * I * character (-k) θ)) =
        -((k : ℂ) * I) * (∫ θ in (0 : ℝ)..2 * Real.pi,
          (f θ : ℂ) * character (-k) θ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      push_cast
      ring
    change _ + (∫ θ in (0 : ℝ)..2 * Real.pi,
      (f θ : ℂ) * (((-k : ℤ) : ℂ) * I * character (-k) θ)) = 0 at h
    rw [hh] at h
    apply sub_eq_zero.mp
    simpa only [character, neg_mul, ← sub_eq_add_neg] using h
  unfold angularCoefficient angularDerivative
  simp only [Complex.ofReal_mul]
  rw [show (fun θ => (Θ : ℂ) * ((deriv (fun u => w (x, u)) θ : ℝ) : ℂ) * character (-k) θ) =
    (fun θ => (Θ : ℂ) * (((deriv f θ : ℝ) : ℂ) * character (-k) θ)) from by funext θ; dsimp [f]; ring]
  rw [intervalIntegral.integral_const_mul, he]
  ring

theorem coefficient_angular_iterate {w : ℝ × ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (Θ : ℝ) (k : ℤ) (x : ℝ) (ℓ : ℕ) :
    angularCoefficient ((angularDerivative Θ)^[ℓ] w) k x =
      ((Θ : ℂ) * (k : ℂ) * I) ^ ℓ * angularCoefficient w k x := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hwℓ : ContDiff ℝ ∞ ((angularDerivative Θ)^[ℓ] w) := mixed_smooth hw Θ 0 ℓ
    have hpℓ : ∀ n θ, ((angularDerivative Θ)^[ℓ] w) (n, θ + 2 * Real.pi) =
        ((angularDerivative Θ)^[ℓ] w) (n, θ) := mixed_periodic hp Θ 0 ℓ
    rw [Function.iterate_succ_apply', coefficient_angularDerivative hwℓ hpℓ, ih, pow_succ]
    ring

theorem coefficient_hasDerivAt {w : ℝ × ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (k : ℤ) (x : ℝ) :
    HasDerivAt (angularCoefficient w k)
      ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        (fderiv ℝ w (x, θ) (1, 0) : ℂ) * character (-k) θ) x := by
  have hdw' : ContDiff ℝ ∞ (fun p : ℝ × ℝ => fderiv ℝ w p (1, 0)) :=
    (hw.fderiv_right (by simp)).clm_apply contDiff_const
  have hdw := hdw'.continuous
  have hc : Continuous (fun p : ℝ × ℝ => (w p : ℂ) * character (-k) p.2) :=
    (Complex.continuous_ofReal.comp hw.continuous).mul
      ((continuous_character _).comp continuous_snd)
  have hc' : Continuous (fun p : ℝ × ℝ =>
      (fderiv ℝ w p (1, 0) : ℂ) * character (-k) p.2) :=
    (Complex.continuous_ofReal.comp hdw).mul
      ((continuous_character _).comp continuous_snd)
  have hd : ∀ u θ, HasDerivAt
      (fun v => (w (v, θ) : ℂ) * character (-k) θ)
      ((fderiv ℝ w (u, θ) (1, 0) : ℂ) * character (-k) θ) u := by
    intro u θ
    have h := (hw.differentiable (by simp) (u, θ)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u θ))
    exact h.ofReal_comp.mul_const _
  exact (Cubic.Analysis.CompactParametricIntegral.hasDerivAt_interval hc hc' hd
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi) x).const_mul _

theorem coefficient_radialDerivative {w : ℝ × ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (k : ℤ) (x : ℝ) :
    angularCoefficient (radialDerivative w) k x =
      (x : ℂ) * deriv (angularCoefficient w k) x := by
  rw [(coefficient_hasDerivAt hw k x).deriv]
  unfold angularCoefficient
  simp_rw [radial_eq_fderiv (hw.differentiable (by simp)), Complex.ofReal_mul,
    mul_assoc (x : ℂ)]
  rw [intervalIntegral.integral_const_mul]
  ring

end Cubic.BoxAsymptotic.SmoothAngularTransform
