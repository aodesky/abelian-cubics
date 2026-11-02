import CubicTargets.PoissonSummation.EulerCorrectionFactor
import Cubic.PoissonSummation.LeadingTermsCorrection

noncomputable section

namespace Cubic.PoissonSummation.EulerCorrectionFactor

theorem R_eq_value (z : ℂ) :
    EulerCorrectionData.R z = HeightZetaCorrectionProduct.value z := rfl

theorem total_correction (z : ℂ) : EulerCorrectionData.E z =
    (1 - (3 : ℂ) ^ (-z)) ^ 2 * EulerCorrectionData.R z := by
  simp only [EulerCorrectionData.E, EulerCorrectionData.R, mul_assoc]

theorem correction_rescaling (z : ℂ) :
    EulerCorrectionData.E z = LeadingTermsData.correction (2 * z) := by
  simp [EulerCorrectionData.E, LeadingTermsData.correction,
    HeightZetaCorrectionProduct.value, HeightZetaCorrectionProduct.inert,
    HeightZetaCorrectionProduct.split, mul_assoc]

theorem «eqn:eulerCorrectionFactor» :
    CubicTargets.PoissonSummation.EulerCorrectionFactor.Claim :=
  ⟨fun z hz => ⟨HeightZetaCorrectionProduct.absolute_inert z hz,
    HeightZetaCorrectionProduct.absolute_split z hz⟩, R_eq_value⟩

/-- The chain factor required by the current manuscript's derivative in `z`. -/
theorem derivative_rescaling (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    deriv EulerCorrectionData.E z = 2 * deriv LeadingTermsData.correction (2 * z) := by
  have hs : 1 < (2 * z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hd := LeadingTermsCorrection.differentiableOn_correction.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hc := hd.hasDerivAt.comp z ((hasDerivAt_id z).const_mul 2)
  have he : EulerCorrectionData.E = fun z : ℂ => LeadingTermsData.correction (2 * z) :=
    funext correction_rescaling
  rw [he]
  simpa only [Function.comp_def, one_mul, mul_comm] using hc.deriv

end Cubic.PoissonSummation.EulerCorrectionFactor
