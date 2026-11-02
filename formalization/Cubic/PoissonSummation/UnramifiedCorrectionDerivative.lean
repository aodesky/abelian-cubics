import Cubic.PoissonSummation.EulerCorrectionFactor
import Cubic.PoissonSummation.LeadingTermsLogDerivative

noncomputable section

namespace Cubic.PoissonSummation.UnramifiedCorrectionDerivative

open EulerCorrectionData

theorem correction_two : LeadingTermsData.correction 2 = (4 / 9 : ℂ) * R 1 := by
  rw [LeadingTermsData.correction]
  norm_num [EulerCorrectionFactor.R_eq_value, Complex.cpow_neg]

theorem R_one_ne_zero : R 1 ≠ 0 := by
  have h := LeadingTermsCorrection.correction_two_ne_zero
  rw [correction_two] at h
  exact (mul_ne_zero_iff.mp h).2

theorem differentiable_R_one : DifferentiableAt ℂ R 1 :=
  HeightZetaCorrectionProduct.differentiableOn_value.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))

theorem log_derivative :
    deriv LeadingTermsData.correction 2 / LeadingTermsData.correction 2 =
      (1 / 2 : ℂ) * (Real.log 3 : ℂ) + deriv R 1 / (2 * R 1) := by
  have hd : HasDerivAt (fun s : ℂ => R (s / 2)) (deriv R 1 / 2) 2 := by
    have hR : HasDerivAt R (deriv R 1) ((2 : ℂ) / 2) := by
      simpa using differentiable_R_one.hasDerivAt
    simpa [Function.comp_def, div_eq_mul_inv] using
      hR.comp (h := fun s : ℂ => s / 2) 2 ((hasDerivAt_id (2 : ℂ)).div_const 2)
  have hr : DifferentiableAt ℂ (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2) 2 := by
    fun_prop
  change logDeriv (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2 * R (s / 2)) 2 = _
  rw [logDeriv_mul 2 (by norm_num [Complex.cpow_neg])
    (by simpa using R_one_ne_zero) hr hd.differentiableAt,
    LeadingTermsLocalDerivatives.ramified_log_derivative, logDeriv_apply, hd.deriv]
  norm_num
  ring

end Cubic.PoissonSummation.UnramifiedCorrectionDerivative
