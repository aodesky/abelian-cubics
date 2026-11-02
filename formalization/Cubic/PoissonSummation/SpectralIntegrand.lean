import Cubic.PoissonSummation.SpectralDecay
import Cubic.PoissonSummation.LocalModelProduct

/-!
# Assembling the computed local Fourier factors

Combine the archimedean logarithmic-coordinate integral with all computed finite
integrals. The factor at three is `1/6`, so multiplication by the explicit scalar
six cancels it. This is algebra of the local transforms, not a proof that the
adelic dual measure is `6 dt`, and not an application of Poisson summation.
-/

noncomputable section

namespace Cubic.PoissonSummation.SpectralIntegrand

open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct LocalModelProduct
open MeasureTheory

/-- All finite local calculations eliminate `s₀`; no specialization of the height was made. -/
theorem finiteFourier_independent_s₀ (s₀ s₀' σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    finiteFourier family s₀ σ t = finiteFourier family s₀' σ t := by
  rw [finiteFourier_claim.spectral_product s₀ σ t hσ,
    finiteFourier_claim.spectral_product s₀' σ t hσ]

/-- The exact local spectral expression, with the exceptional factor cancellation checked.
The scalar six is explicit; its dual-measure interpretation is in `lemma:poissonIntegral`. -/
theorem six_mul_local_product (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    6 * ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t =
      (s₀ + 2 * σ) /
        ((s₀ + 2 * Real.pi * Complex.I * t) * (2 * spectralParameter σ t)) *
        (∏' q : InertPrimes, inertFactor q (spectralParameter σ t)) *
        (∏' p : SplitPrimes, splitFactor p (spectralParameter σ t)) := by
  rw [ArchimedeanFourier.fourier_eq_spectralParameter s₀ σ t h₀ (lt_trans zero_lt_one hσ),
    finiteFourier_claim.spectral_product s₀ σ t hσ]
  unfold value
  ring

/-- The product of actual finite local Fourier integrals is continuous in `t`. -/
theorem continuous_finiteFourier (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Continuous (finiteFourier family s₀ σ) := by
  have heq : finiteFourier family s₀ σ = fun t => value (spectralParameter σ t) :=
    funext (fun t => finiteFourier_claim.spectral_product s₀ σ t hσ)
  rw [heq]
  exact continuous_value_spectralParameter σ hσ

/-- Absolute convergence of the spectral product of the computed local integrals.
This does not presuppose a global Fourier factorization or Poisson formula. -/
theorem integrable_local_product (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (fun t : ℝ => ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t) := by
  apply (ArchimedeanFourier.integrable_fourier s₀ σ h₀ (lt_trans zero_lt_one hσ)).mul_bdd
    (continuous_finiteFourier s₀ σ hσ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => finiteFourier_claim.domination s₀ σ t hσ)

/-- The explicit scalar six preserves the proved convergence of the spectral integral. -/
theorem integrable_six_mul_local_product (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (fun t : ℝ => 6 * ArchimedeanFourier.fourier s₀ σ t * finiteFourier family s₀ σ t) := by
  simpa only [mul_assoc] using (integrable_local_product s₀ σ h₀ hσ).const_mul (6 : ℂ)

end Cubic.PoissonSummation.SpectralIntegrand
