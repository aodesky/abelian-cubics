import Cubic.Counting.AsymptoticConstants
import Cubic.Counting.AsymptoticConstantIdentities
import Cubic.Counting.AsymptoticConstantScaling
import Cubic.Counting.EulerKroneckerGamma

/-!
# The constants of `thm:asymptoticPolynomialCount`

Both displayed presentations of the constants, the Gamma evaluation, and all
product/sum convergence clauses are proved without the Poisson summation input.
The last lemmas attach them to any Laurent expansion of the height series. The counting asymptotic is assembled in
`Cubic.Counting.AsymptoticPolynomialCount`.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstantsAssembly

open AsymptoticConstantsData AsymptoticConstantsConvergence AsymptoticConstantIdentities

theorem constants_of_gamma (hγ : CubicTargets.Counting.EulerKroneckerGamma.Claim) :
    CubicTargets.Counting.AsymptoticPolynomialCount.Constants EulerKroneckerCalculation.value
      originalLeading (originalLeading * originalSecondaryRatio) := by
  have hC := original_leading_positive.ne'
  have hratio : originalLeading * originalSecondaryRatio / originalLeading =
      originalSecondaryRatio := by field_simp
  refine {
    positive := original_leading_positive
    original_leading := rfl
    simplified_leading := leading_formulas
    original_secondary := hratio
    simplified_secondary := ?_
    gamma_evaluation := hγ
    inert_product_absolute := inert_product_absolute
    split_product_absolute := split_product_absolute
    simplified_product_absolute := simplified_product_absolute
    inert_sum_absolute := inert_sum_absolute
    split_sum_absolute := split_sum_absolute
    simplified_sum_absolute := simplified_sum_absolute }
  have he := secondary_formulas EulerKroneckerCalculation.value
  change EulerKroneckerCalculation.value = (classicalEulerKronecker : ℂ) at hγ
  rw [hγ, sub_self, add_zero] at he
  simpa only [Complex.ofReal_div, hγ] using
    (congrArg (fun x : ℝ => (x : ℂ)) hratio).trans he

theorem constants :
    CubicTargets.Counting.AsymptoticPolynomialCount.Constants EulerKroneckerCalculation.value
      originalLeading (originalLeading * originalSecondaryRatio) :=
  constants_of_gamma EulerKroneckerGamma.evaluation

theorem constants_of_continuation {Z : ℂ → ℂ} {γ : ℂ}
    (h : CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker Z γ) :
    CubicTargets.Counting.AsymptoticPolynomialCount.Constants γ
      originalLeading (originalLeading * originalSecondaryRatio) := by
  rw [EulerKroneckerCalculation.unique h]
  exact constants

variable {Z F : ℂ → ℂ} {γ c₂ c₁ : ℂ}
  (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion Z F γ c₂ c₁)

include h

/-- The subleading Laurent coefficient gives exactly the displayed `D`. -/
theorem secondary_from_laurent : secondaryFromLaurent c₂ c₁ =
    ((originalLeading * originalSecondaryRatio : ℝ) : ℂ) := by
  have hr := AsymptoticConstants.secondary_original_of_gamma h
    (EulerKroneckerGamma.of_continuation (AsymptoticConstants.eulerKronecker h))
  rw [AsymptoticConstants.leading_original h] at hr
  have hn : (originalLeading : ℂ) ≠ 0 := by
    exact_mod_cast original_leading_positive.ne'
  rw [div_eq_iff hn] at hr
  simpa only [Complex.ofReal_mul, mul_comm] using hr

/-- The Laurent-derived main term is the real main term in `thm:asymptoticPolynomialCount`.
This is a constants identity; it does not assert a counting asymptotic. -/
theorem root_main_term (H : ℝ) :
    AsymptoticConstantScaling.rootPolynomialMainTerm c₂ c₁ H =
      ((originalLeading * H ^ 2 * Real.log H +
        (originalLeading * Real.log (Real.sqrt 3) +
          originalLeading * originalSecondaryRatio - Real.pi / (3 * Real.sqrt 3)) *
            H ^ 2 : ℝ) : ℂ) := by
  rw [AsymptoticConstantScaling.rootPolynomialMainTerm,
    AsymptoticConstants.leading_original h, secondary_from_laurent h]
  push_cast
  rfl

end Cubic.Counting.AsymptoticConstantsAssembly
