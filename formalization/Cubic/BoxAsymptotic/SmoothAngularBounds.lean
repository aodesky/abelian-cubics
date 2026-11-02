import Cubic.BoxAsymptotic.SmoothTransformData
import Cubic.BoxAsymptotic.SmoothArcGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The factor `Θ` in the transform estimate comes from the length of the
angular support. The argument is uniform in the arc center, including arcs
which cross the endpoint of the chosen representative interval. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothAngularBounds

open Set MeasureTheory Complex
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.BoxAsymptotic.SmoothTransformData

theorem character_periodic (k : ℤ) : Function.Periodic (character k) (2 * Real.pi) := by
  intro θ
  simp [character, Complex.ofReal_add, Complex.ofReal_mul, add_mul,
    Complex.exp_add, Complex.exp_two_pi_mul_I]

theorem integral_norm_le {f : ℝ → ℂ} {Θ θ₀ M : ℝ}
    (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : Function.Periodic f (2 * Real.pi))
    (hb : ∀ θ, ‖f θ‖ ≤ M)
    (hs : ∀ θ, f θ ≠ 0 → |wrap (θ - θ₀)| ≤ 4 * Θ) :
    ‖∫ θ in (0 : ℝ)..2 * Real.pi, f θ‖ ≤ M * (8 * Θ) := by
  have hshift := hp.intervalIntegral_add_eq 0 (θ₀ - Real.pi)
  rw [zero_add, show θ₀ - Real.pi + 2 * Real.pi = θ₀ + Real.pi by ring] at hshift
  rw [hshift, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  let T := Ioc (θ₀ - Real.pi) (θ₀ + Real.pi)
  let S := T ∩ Icc (θ₀ - 4 * Θ) (θ₀ + 4 * Θ)
  have heq : (∫ θ in T, f θ) = ∫ θ in S, f θ := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc inter_subset_left
    intro θ hθ
    by_contra hn
    have hwrap : wrap (θ - θ₀) = θ - θ₀ := by
      apply (toIocMod_eq_self Real.two_pi_pos).mpr
      have ht := hθ.1
      change θ₀ - Real.pi < θ ∧ θ ≤ θ₀ + Real.pi at ht
      constructor <;> linarith [ht.1, ht.2]
    have hh := hs θ hn
    rw [hwrap, abs_le] at hh
    apply hθ.2
    exact ⟨hθ.1, ⟨by linarith [hh.1], by linarith [hh.2]⟩⟩
  change ‖∫ θ in T, f θ‖ ≤ _
  rw [heq]
  have hfin : volume S < ⊤ :=
    (measure_mono (show S ⊆ Icc (θ₀ - 4 * Θ) (θ₀ + 4 * Θ) from inter_subset_right)).trans_lt
      isCompact_Icc.measure_lt_top
  have hm : volume.real S ≤ 8 * Θ := by
    have h := measureReal_mono (μ := volume)
      (show S ⊆ Icc (θ₀ - 4 * Θ) (θ₀ + 4 * Θ) from inter_subset_right)
      isCompact_Icc.measure_ne_top
    rw [Real.volume_real_Icc_of_le (by linarith : θ₀ - 4 * Θ ≤ θ₀ + 4 * Θ)] at h
    linarith
  exact (norm_setIntegral_le_of_norm_le_const hfin (fun θ _ => hb θ)).trans
    (mul_le_mul_of_nonneg_left hm hM)

theorem coefficient_norm_le {w : ℝ × ℝ → ℝ} {Θ θ₀ M : ℝ}
    (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hb : ∀ p, |w p| ≤ M)
    (hs : Function.support w ⊆ {p | |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (k : ℤ) (x : ℝ) :
    ‖angularCoefficient w k x‖ ≤ (4 / Real.pi) * M * Θ := by
  have hper : Function.Periodic
      (fun θ => (w (x, θ) : ℂ) * character (-k) θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [hp, character_periodic (-k)]
  have hbound : ∀ θ, ‖(w (x, θ) : ℂ) * character (-k) θ‖ ≤ M := by
    intro θ
    simpa only [norm_mul, norm_character, mul_one, Complex.norm_real, Real.norm_eq_abs]
      using hb (x, θ)
  have hsupp : ∀ θ, (w (x, θ) : ℂ) * character (-k) θ ≠ 0 →
      |wrap (θ - θ₀)| ≤ 4 * Θ := by
    intro θ hn
    have hz : w (x, θ) ≠ 0 := fun hzero => hn (by simp [hzero])
    exact hs hz
  have h := integral_norm_le hΘ hM hper hbound hsupp
  rw [angularCoefficient, norm_mul, norm_inv, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (M * (8 * Θ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp; ring

end Cubic.BoxAsymptotic.SmoothAngularBounds
