import Cubic.Counting.IntegralPointCountData
import Cubic.Counting.GeneralMonicData
import Cubic.Counting.AsymptoticConstantsAssembly

/-! Exact identities between the proved coefficient main terms and the current
manuscript's single polynomial Q. No asymptotic estimate is assumed here. -/

noncomputable section

namespace Cubic.Counting.CountPolynomialNormalization

open IntegralPointCountData GeneralMonicData AsymptoticConstantsData
open Cubic.PoissonSummation

theorem C_eq_alpha : Cconst = alpha / 3 := by
  simpa [Cconst, simplifiedLeading, alpha, div_eq_mul_inv, mul_comm] using
    AsymptoticConstantsAssembly.constants.simplified_leading

theorem Q_eq (μ : ℂ) (hμ : μ = EulerKroneckerCalculation.value) (X : ℝ) :
    Q μ X = 2 * Cconst / 3 * X + 2 * Dconst / 3 := by
  subst μ
  have hc := AsymptoticConstantsAssembly.constants
  have hr : Dconst / Cconst =
      EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
        beta + 3 / 8 * Real.log 3 - 1 / 2 := by
    have hs : ((Dconst / Cconst : ℝ) : ℂ) =
        simplifiedSecondaryRatio EulerKroneckerCalculation.value := by
      simpa only [Cconst, Dconst, Complex.ofReal_div] using hc.simplified_secondary
    have h := congrArg Complex.re hs
    have he : (simplifiedSecondaryRatio EulerKroneckerCalculation.value).re =
        EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
          beta + 3 / 8 * Real.log 3 - 1 / 2 := by
      unfold simplifiedSecondaryRatio beta
      rw [← Complex.ofReal_tsum]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
      norm_num only [Complex.mul_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.normSq_ofNat]
      ring
    rw [Complex.ofReal_re, he] at h
    exact h
  have hD : Dconst = Cconst *
      (EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
        beta + 3 / 8 * Real.log 3 - 1 / 2) := by
    have hn : Cconst ≠ 0 := hc.positive.ne'
    rw [div_eq_iff hn] at hr
    simpa only [mul_comm] using hr
  rw [hD, C_eq_alpha, Q]
  ring

theorem Q_of_expansion {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ}
    (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion D F μ c₂ c₁) (X : ℝ) :
    Q μ X = 2 * Cconst / 3 * X + 2 * Dconst / 3 :=
  Q_eq μ (EulerKroneckerCalculation.unique (AsymptoticConstants.eulerKronecker h)) X

theorem summatory_main (X : ℝ) :
    Cconst / 3 * X * Real.log X + 2 * Dconst / 3 * X =
      X * Q EulerKroneckerCalculation.value (1 / 2 * Real.log X) := by
  rw [Q_eq _ rfl]
  ring

theorem trace_one_main (X : ℝ) :
    Cconst / 6 * X * Real.log X + (Dconst / 3 - Real.pi / (9 * Real.sqrt 3)) * X =
      1 / 2 * X * Q EulerKroneckerCalculation.value (1 / 2 * Real.log X) -
        Real.pi / (9 * Real.sqrt 3) * X := by
  rw [Q_eq _ rfl]
  ring

theorem trace_zero_main (X : ℝ) :
    5 * Cconst / 6 * X * Real.log X +
      (5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3 - Real.pi / (3 * Real.sqrt 3)) * X =
    5 / 2 * X * Q EulerKroneckerCalculation.value (1 / 2 * Real.log X) -
      (alpha / 4 * Real.log 3 + Real.pi / (3 * Real.sqrt 3)) * X := by
  rw [Q_eq _ rfl, C_eq_alpha]
  ring

theorem laurent_main {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ}
    (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion D F μ c₂ c₁) (X : ℝ) :
    c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X =
      ((X * Q μ (1 / 2 * Real.log X) : ℝ) : ℂ) := by
  have hc := AsymptoticConstants.leading_original h
  have hd := AsymptoticConstantsAssembly.secondary_from_laurent h
  rw [leadingFromLaurent] at hc
  rw [secondaryFromLaurent] at hd
  rw [Q_of_expansion h]
  dsimp [Cconst, Dconst]
  push_cast at hc hd ⊢
  linear_combination (X * Real.log X : ℂ) * hc / 3 + (2 * X : ℂ) * hd / 3

theorem irreducible_main {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ}
    (h : CubicTargets.PoissonSummation.LeadingTerms.Expansion D F μ c₂ c₁) (X : ℝ) :
    c₂ / 8 * X * Real.log X +
      (c₁ / 4 - c₂ / 8 - ((Real.pi / (9 * Real.sqrt 3) : ℝ) : ℂ)) * X =
      ((1 / 2 * X * Q μ (1 / 2 * Real.log X) - Real.pi / (9 * Real.sqrt 3) * X : ℝ) : ℂ) := by
  have he := laurent_main h X
  push_cast at he ⊢
  linear_combination he / 2

end Cubic.Counting.CountPolynomialNormalization
