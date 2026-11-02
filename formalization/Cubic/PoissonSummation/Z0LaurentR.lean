import CubicTargets.PoissonSummation.Z0LaurentR
import Cubic.PoissonSummation.LeadingTermsNormalization
import Cubic.PoissonSummation.UnramifiedCorrectionDerivative

noncomputable section

namespace Cubic.PoissonSummation.Z0LaurentR

theorem «eqn:Z0LaurentR» : CubicTargets.PoissonSummation.Z0LaurentR.Claim := by
  intro D F μ c₂ c₁ h
  dsimp only
  have hs := (div_eq_iff h.leading_ne_zero).mp h.subleading
  rw [UnramifiedCorrectionDerivative.log_derivative] at hs
  have hl := h.leading
  rw [UnramifiedCorrectionDerivative.correction_two] at hl
  have ho := LeadingTermsNormalization.laurent_z h
  rw [hs, hl] at ho
  convert ho using 1
  ext z
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Cubic.PoissonSummation.Z0LaurentR
