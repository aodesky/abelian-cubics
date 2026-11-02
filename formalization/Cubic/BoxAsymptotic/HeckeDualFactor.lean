import Cubic.BoxAsymptotic.HeckeCosineWeights

/-! Uniform control of the finite-conductor part of the dual AFE prefactor.
The remaining Gamma quotient is the explicitly cited generic Stirling bound.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeDualFactor

open Cubic.Analysis.GammaAFEData
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeCosineAFE
open Cubic.BoxAsymptotic.HeckeCosineWeights

theorem conductor_power {Q σ : ℝ} (hQ : 0 < Q) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 4) :
    Q ^ (1 - 2 * σ) ≤ 1 + Q⁻¹ := by
  by_cases h : 1 ≤ Q
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr hQ.le))
  · have hr : Q ^ (1 - 2 * σ) ≤ Q ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hQ (le_of_not_ge h) (by linarith)
    norm_num only [Real.rpow_neg_one] at hr
    linarith

def conductorBound : ℝ := 1 + (Real.sqrt 3 / (2 * Real.pi))⁻¹ +
  (Real.sqrt 27 / (2 * Real.pi))⁻¹

theorem conductorBound_pos : 0 < conductorBound := by unfold conductorBound; positivity

theorem conductor_scale_bound (k : ℤ) : 1 + (conductorScale k)⁻¹ ≤ conductorBound := by
  unfold conductorScale conductorBound
  split_ifs
  · exact le_add_of_nonneg_right (by positivity)
  · have h : 0 ≤ (Real.sqrt 3 / (2 * Real.pi))⁻¹ := by positivity
    linarith

theorem bound (hGamma : CubicTargets.BoxAsymptotic.GammaAFE.GammaRatio) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (ε s : ℂ),
      2 ≤ k → ‖ε‖ = 1 → 1 / 2 ≤ s.re → s.re ≤ 3 / 4 →
      ‖dualFactor (conductorScale k) (gammaShift k) ε s‖ ≤
        C * modeLength k s ^ (1 - 2 * s.re) := by
  obtain ⟨C, hC, hb⟩ := hGamma
  refine ⟨conductorBound * C, mul_pos conductorBound_pos hC, fun k ε s hk hε hs hs' => ?_⟩
  have hQ := conductorScale_pos k
  have hq := (conductor_power hQ hs hs').trans (conductor_scale_bound k)
  have hγ := hb (gammaShift k) s (gammaShift_ge_one hk) hs hs'
  rw [dualFactor, norm_mul, norm_mul, hε, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have hre : (1 - 2 * s).re = 1 - 2 * s.re := by simp
  rw [hre]
  exact (mul_le_mul hq hγ (norm_nonneg _) conductorBound_pos.le).trans_eq (by
    unfold modeLength
    ring)

end Cubic.BoxAsymptotic.HeckeDualFactor
