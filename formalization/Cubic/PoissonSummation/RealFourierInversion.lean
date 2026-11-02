import Cubic.PoissonSummation.SpectralIntegrand
import Mathlib.Analysis.Fourier.Inversion

/-!
# Reusing mathlib Fourier inversion in the logarithmic coordinate

Check that the actual archimedean transform has mathlib's Fourier convention,
then apply its existing `L¹` inversion theorem. For the full height series,
`at_zero_of_spectral_identity` isolates what remains after the analytic bounds:
an integrable periodization continuous at zero and its genuine Fourier identity.
It does not define the periodization by its proposed transform, assume Poisson,
or establish the quotient and measure identifications.
-/

noncomputable section

namespace Cubic.PoissonSummation

open MeasureTheory
open scoped FourierTransform

namespace ArchimedeanFourier

/-- The inverse-character convention agrees with mathlib, including the `2π`.
This identity of totalized integrals does not by itself assert integrability. -/
theorem fourier_eq_mathlib (s₀ σ : ℂ) : fourier s₀ σ = 𝓕 (inverseHeight s₀ σ) := by
  ext t
  rw [fourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  simp only [integrand, character, Circle.coe_exp, smul_eq_mul]
  rw [← Complex.exp_neg, mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- Inversion for the constructed height, using mathlib's theorem without positivity-type
or symmetry assumptions on the complex parameters. -/
theorem fourier_inversion (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) (u : ℝ) :
    ∫ t : ℝ, ((character t u : Circle) : ℂ) * fourier s₀ σ t = inverseHeight s₀ σ u := by
  have h := (integrable_inverseHeight s₀ σ h₀ hσ).fourierInv_fourier_eq
    (by rw [← fourier_eq_mathlib]; exact integrable_fourier s₀ σ h₀ hσ)
    ((continuous_inverseHeight s₀ σ).continuousAt (x := u))
  rw [Real.fourierInv_eq', ← fourier_eq_mathlib] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [character, Circle.coe_exp, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

end ArchimedeanFourier

namespace RealFourierInversion

open CubicTargets.PoissonSummation.FiniteFourierProduct
open LocalModelProduct

/-- Conditional application of existing Fourier inversion to the future periodization.
The `L¹` condition on its transform is discharged by our local spectral estimates.
The spatial `L¹`, continuity, and Fourier identity remain explicit prerequisites. -/
theorem at_zero_of_spectral_identity (F : ℝ → ℂ) (s₀ σ : ℂ)
    (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) (hF : Integrable F) (hF₀ : ContinuousAt F 0)
    (htransform : ∀ t : ℝ, 𝓕 F t =
      6 * ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t) :
    F 0 = 6 * ∫ t : ℝ, ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t := by
  have hFi : Integrable (𝓕 F) := by
    simpa only [funext htransform] using SpectralIntegrand.integrable_six_mul_local_product s₀ σ h₀ hσ
  have h := hF.fourierInv_fourier_eq hFi hF₀
  rw [Real.fourierInv_eq'] at h
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, htransform] at h
  rw [show (fun t : ℝ => 6 * ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t) =
    (fun t : ℝ => 6 * (ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t)) by
      ext; ring, integral_const_mul] at h
  exact h.symm

end RealFourierInversion
end Cubic.PoissonSummation
