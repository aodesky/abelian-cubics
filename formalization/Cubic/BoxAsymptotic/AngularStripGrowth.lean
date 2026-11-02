import Cubic.BoxAsymptotic.HeckeAnalyticRealization
import Cubic.BoxAsymptotic.AngularCorrectionBounds

/-! Individual polynomial growth of the nonzero angular continuations. These
bounds justify contour shifts and handle the finitely many small modes. The
exponents may depend on a fixed frequency, but are independent of `η`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularStripGrowth

open Complex
open Cubic.BoxAsymptotic.HeckeAnalyticRealization
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters

theorem correction_bound {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (k : ℤ) {s : ℂ} (hs : 1 / 2 + η ≤ s.re) :
    ‖AngularCorrectionProduct.value k s‖ ≤
      AngularCorrectionBounds.absoluteConstant * η⁻¹ ^ 4 := by
  have hv := AngularCorrectionBounds.value_bound k (s := s) (by linarith)
  have hz := Cubic.Analysis.ZetaStripGrowth.riemannZeta_real_le (2 * s.re) (by linarith)
  have hi : 2 ≤ η⁻¹ := by
    rw [← one_div, le_div_iff₀ hη]
    linarith
  have hh : 1 / (2 * s.re - 1) ≤ (1 / 2) * η⁻¹ := by
    calc
      _ ≤ 1 / (2 * η) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = _ := by field_simp
  have hz' : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤ η⁻¹ := by linarith
  calc
    _ ≤ ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ^ 3 *
        AngularCorrectionBounds.absoluteConstant := hv
    _ ≤ η⁻¹ ^ 3 * AngularCorrectionBounds.absoluteConstant :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz' 3)
        AngularCorrectionBounds.absoluteConstant_pos.le
    _ ≤ η⁻¹ ^ 4 * AngularCorrectionBounds.absoluteConstant :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith : 1 ≤ η⁻¹)
        (by decide : 3 ≤ 4)) AngularCorrectionBounds.absoluteConstant_pos.le
    _ = _ := mul_comm _ _

theorem primitive_growth
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    PrimitiveHeckeData.PolynomialVerticalGrowth (primitiveL hHecke k) := by
  rw [primitiveL, dif_pos ⟨hk, hk0⟩]
  exact (exists_analytic hHecke hk hk0).choose_spec.choose_spec.choose_spec.growth

theorem hecke_growth
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖heckeL hHecke k s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨C, hC, N, hN⟩ := primitive_growth hHecke hk hk0 (1 / 2) 2 (by norm_num)
  refine ⟨2 * C, by positivity, N, fun s hlo hhi => ?_⟩
  rw [heckeL, norm_mul]
  calc
    _ ≤ 2 * (C * (1 + |s.im|) ^ N) :=
      mul_le_mul (HeckeOmitThree.factor_bound k s (by linarith))
        (hN s hlo hhi) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem angular_growth
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (k : ℤ) (hk0 : k ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (η : ℝ), 0 < η → η ≤ 1 / 4 →
      ∀ s : ℂ, 1 / 2 + η ≤ s.re → s.re ≤ 2 →
        ‖angularF hHecke k s‖ ≤ C * η⁻¹ ^ 4 * (1 + |s.im|) ^ N := by
  by_cases hk : Even k
  · obtain ⟨C₁, hC₁, N₁, h₁⟩ := hecke_growth hHecke hk hk0
    obtain ⟨C₂, hC₂, N₂, h₂⟩ := hecke_growth hHecke (hk.mul_left 3)
      (mul_ne_zero (by norm_num) hk0)
    refine ⟨2 * C₁ * C₂ * AngularCorrectionBounds.absoluteConstant,
      by positivity [AngularCorrectionBounds.absoluteConstant_pos], N₁ + N₂, ?_⟩
    intro η hη hη' s hlo hhi
    rw [angularF, if_pos hk, norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ 2 * ((C₁ * (1 + |s.im|) ^ N₁) * (C₂ * (1 + |s.im|) ^ N₂) *
          (AngularCorrectionBounds.absoluteConstant * η⁻¹ ^ 4)) :=
        mul_le_mul (AngularFactorBounds.localFactor_bound k s (by linarith))
          (mul_le_mul
            (mul_le_mul (h₁ s (by linarith) hhi) (h₂ s (by linarith) hhi)
              (norm_nonneg _) (by positivity))
            (correction_bound hη hη' k hlo) (norm_nonneg _) (by positivity))
          (by positivity) (by norm_num)
      _ = _ := by rw [pow_add]; ring
  · refine ⟨1, by norm_num, 0, fun η hη _ s _ _ => ?_⟩
    simp only [angularF, if_neg hk, norm_zero, pow_zero, mul_one, one_mul]
    positivity

end Cubic.BoxAsymptotic.AngularStripGrowth
