import Cubic.Counting.AsymptoticConstantsConvergence
import Cubic.PoissonSummation.LeadingTermsLogDerivative
import Cubic.PoissonSummation.LeadingTermsSimplifiedDerivative

/-!
# Equality of the original and simplified constant expressions

These identities use neither the Poisson summation input nor the counting
asymptotic, only the convergence and logarithmic differentiation of the Euler
products. The evaluation of the Euler–Kronecker constant by Gamma values is in
`EulerKroneckerGamma`.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstantIdentities

open Cubic.PoissonSummation Cubic.PoissonSummation.FiniteEulerProduct
open AsymptoticConstantsData AsymptoticConstantsConvergence

theorem original_leading_correction : (originalLeading : ℂ) =
    (Real.pi : ℂ) ^ 2 / 9 * LeadingTermsData.correction 2 := by
  rw [LeadingTermsCorrection.correction_two]
  simp only [originalLeading, inert_factor_eq, split_factor_eq]
  push_cast
  ring

theorem leading_formulas : originalLeading = simplifiedLeading := by
  apply Complex.ofReal_injective
  rw [original_leading_correction, LeadingTermsEulerProduct.correction_two_explicit]
  simp only [simplifiedLeading, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, simplified_product_cast]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  norm_num

theorem original_leading_positive : 0 < originalLeading := by
  have he := congrArg Complex.re original_leading_correction
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_mul, sub_zero] at he
  have hr : originalLeading = Real.pi ^ 2 / 9 * (LeadingTermsData.correction 2).re := by
    simpa using he
  rw [hr]
  exact mul_pos (by positivity) LeadingTermsCorrection.correction_two_pos

/-- This is precisely the prime contribution to `D/C`, before evaluating `γ_E`. -/
theorem prime_sum_identity :
    (1 / 2 : ℂ) * (Real.log 3 : ℂ) +
      (∑' q : InertPrimes, (inertLogTerm q : ℂ)) +
      3 * (∑' p : SplitPrimes, (originalSplitLogTerm p : ℂ)) =
    -deriv riemannZeta 2 / riemannZeta 2 + (3 / 8 : ℂ) * (Real.log 3 : ℂ) +
      ∑' p : SplitPrimes, (simplifiedSplitLogTerm p : ℂ) := by
  have h := LeadingTermsLogDerivative.correction_log_derivative.symm.trans
    LeadingTermsSimplifiedDerivative.correction_log_derivative
  simp_rw [← inert_log_cast, ← original_split_log_cast, ← simplified_log_cast] at h
  rw [tsum_mul_left] at h
  exact h

/-- The two secondary expressions differ only in the evaluation of `γ_E`. -/
theorem secondary_formulas (γ : ℂ) :
    (originalSecondaryRatio : ℂ) = simplifiedSecondaryRatio γ +
      ((classicalEulerKronecker : ℂ) - γ) := by
  have h := prime_sum_identity
  simp only [originalSecondaryRatio, simplifiedSecondaryRatio]
  push_cast
  linear_combination h

end Cubic.Counting.AsymptoticConstantIdentities
