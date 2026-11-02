import Cubic.Counting.AsymptoticConstantsConvergence
import Cubic.PoissonSummation.LeadingTerms
import Cubic.PoissonSummation.LeadingTermsLogDerivative
import CubicTargets.Counting.AsymptoticPolynomialCount

/-!
# The constants of `thm:asymptoticPolynomialCount` from the Laurent expansion

These calculations express the constants of `thm:asymptoticPolynomialCount`
through the Laurent coefficients of the height series; they do not involve the
counting asymptotic. The input `Expansion` records a Laurent expansion of the
height series and the continuation of the Dedekind zeta function of `ℚ(√-3)`;
`prop:leadingTerms` supplies it, relative to the Poisson summation input `PoissonWithDualMeasure.BlackBox`.

The secondary coefficient is expressed through the Euler–Kronecker constant
characterized by that continuation. Its evaluation by Gamma values is in
`EulerKroneckerGamma`.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstants

open Cubic.PoissonSummation Cubic.PoissonSummation.FiniteEulerProduct
open AsymptoticConstantsData AsymptoticConstantsConvergence

theorem secondary_ratio (c₂ c₁ : ℂ) (hc₂ : c₂ ≠ 0) :
    secondaryFromLaurent c₂ c₁ / leadingFromLaurent c₂ = c₁ / c₂ - 1 / 2 := by
  dsimp [secondaryFromLaurent, leadingFromLaurent]
  field_simp

variable {Z F : ℂ → ℂ} {γ c₂ c₁ : ℂ}
  (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion Z F γ c₂ c₁)

include h

theorem leading_simplified : leadingFromLaurent c₂ = (simplifiedLeading : ℂ) := by
  rw [leadingFromLaurent, h.explicit_leading]
  simp only [simplifiedLeading, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, simplified_product_cast]
  ring

theorem leading_original : leadingFromLaurent c₂ = (originalLeading : ℂ) := by
  rw [leadingFromLaurent, h.leading, h.residue_L_value, h.residue_value,
    LeadingTermsCorrection.correction_two]
  simp only [originalLeading, inert_factor_eq, split_factor_eq]
  push_cast
  have hsqrt : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt0 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp
  rw [hsqrt]
  ring

theorem leading_formulas_agree : originalLeading = simplifiedLeading := by
  apply Complex.ofReal_injective
  exact (leading_original h).symm.trans (leading_simplified h)

theorem leading_positive : 0 < originalLeading := by
  have he := leading_original h
  rw [leadingFromLaurent, h.leading, h.residue_L_value, h.residue_value] at he
  have hpi : 0 < Real.pi / (3 * Real.sqrt 3) := by positivity
  have hc : LeadingTermsData.correction 2 =
      ((LeadingTermsData.correction 2).re : ℂ) := by
    apply Complex.ext <;> simp [LeadingTermsCorrection.correction_two_real]
  rw [hc] at he
  have hr : (3 / 4 : ℝ) * (4 * (Real.pi / (3 * Real.sqrt 3)) ^ 2 *
      (LeadingTermsData.correction 2).re) = originalLeading := by
    apply Complex.ofReal_injective
    push_cast
    exact he
  rw [← hr]
  exact mul_pos (by norm_num) (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hpi))
    LeadingTermsCorrection.correction_two_pos)

theorem secondary_simplified :
    secondaryFromLaurent c₂ c₁ / leadingFromLaurent c₂ = simplifiedSecondaryRatio γ := by
  rw [secondary_ratio c₂ c₁ h.leading_ne_zero, h.explicit_subleading]
  simp only [simplifiedSecondaryRatio, simplified_log_cast]
  ring

/-- The original prime-sum formula, before the Gamma evaluation of `γ`. -/
theorem secondary_original :
    secondaryFromLaurent c₂ c₁ / leadingFromLaurent c₂ =
      γ + (1 / 2 : ℂ) * (Real.log 3 : ℂ) +
      (∑' q : InertPrimes, (inertLogTerm q : ℂ)) +
      3 * (∑' p : SplitPrimes, (originalSplitLogTerm p : ℂ)) - 1 / 2 := by
  rw [secondary_ratio c₂ c₁ h.leading_ne_zero, h.subleading,
    LeadingTermsLogDerivative.correction_log_derivative]
  simp_rw [← inert_log_cast, ← original_split_log_cast]
  rw [tsum_mul_left]
  ring

/-- The original displayed ratio, given the Gamma evaluation of `γ`. -/
theorem secondary_original_of_gamma
    (hγ : γ = (classicalEulerKronecker : ℂ)) :
    secondaryFromLaurent c₂ c₁ / leadingFromLaurent c₂ = (originalSecondaryRatio : ℂ) := by
  rw [secondary_original h, hγ]
  simp [originalSecondaryRatio, Complex.ofReal_tsum]

/-- `γ` is the Euler–Kronecker constant of the Dedekind zeta function of `ℚ(√-3)`. -/
theorem eulerKronecker : CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker Z γ :=
  ⟨h.dedekind_agrees, h.dedekind_analytic, h.euler_kronecker⟩

end Cubic.Counting.AsymptoticConstants
