import CubicTargets.PoissonSummation.Z0Laurent
import Cubic.PoissonSummation.LeadingTermsNormalization
import Cubic.Counting.AsymptoticConstantsConvergence

noncomputable section

namespace Cubic.PoissonSummation.Z0Laurent

open Cubic.Counting.IntegralPointCountData
open Cubic.Counting.AsymptoticConstantsConvergence

theorem alpha_cast : (alpha : ℂ) = LeadingTermsData.splitProductAtTwo :=
  simplified_product_cast

theorem beta_cast : (beta : ℂ) = ∑' p : FiniteEulerProduct.SplitPrimes,
    LeadingTermsData.splitLogTerm p := by
  rw [beta, Complex.ofReal_tsum]
  simp only [simplified_log_cast]

theorem leading_coefficient {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ}
    (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion D F μ c₂ c₁) :
    c₂ = 4 * (alpha : ℂ) / 9 := by rw [h.explicit_leading, alpha_cast]; ring

theorem subleading_coefficient {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ}
    (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion D F μ c₂ c₁) :
    c₁ = 4 * (alpha : ℂ) / 9 * (μ - deriv riemannZeta 2 / riemannZeta 2 +
      (beta : ℂ) + 3 / 8 * (Real.log 3 : ℂ)) := by
  have hs := (div_eq_iff h.leading_ne_zero).mp h.explicit_subleading
  rw [leading_coefficient h, ← beta_cast] at hs
  linear_combination hs

theorem «eqn:Z0Laurent» : CubicTargets.PoissonSummation.Z0Laurent.Claim := by
  intro D F μ c₂ c₁ h
  have ho := LeadingTermsNormalization.laurent_z h
  rw [leading_coefficient h, subleading_coefficient h] at ho
  convert ho using 1
  ext z
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Cubic.PoissonSummation.Z0Laurent
