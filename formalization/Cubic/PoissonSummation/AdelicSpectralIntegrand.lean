import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.ArchimedeanTorusFourier
import Cubic.PoissonSummation.SpectralIntegrand

/-!
# Spectral integrability for the original local Fourier components

The spectral integrand is the product of the actual archimedean Haar integral
and the product of the actual finite Haar integrals. Transfer the proved decay
and domination estimates to these original objects. `AdelicFourierIntegral`
proves equality with the independently defined global adelic Fourier integral.
The Poisson identity is applied in `lemma:poissonIntegral`.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicSpectralIntegrand

open MeasureTheory

def integrand (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  ArchimedeanHaarData.fourier ArchimedeanHaar.measure s₀ σ t *
    AdelicFourierComponents.finiteFourier s₀ σ t

theorem integrand_eq_coordinate (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    integrand s₀ σ t = ArchimedeanFourier.fourier s₀ σ t *
      CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier
        LocalModelProduct.family s₀ σ t := by
  rw [integrand, ArchimedeanTorusFourier.fourier_eq_coordinate _ ArchimedeanHaar.normalized
    s₀ σ t h₀ (lt_trans zero_lt_one hσ),
    show AdelicFourierComponents.finiteFourier s₀ σ t =
      FiniteEulerProduct.value (FiniteEulerProduct.spectralParameter σ t) from
        AdelicFourierComponents.finite_integrals_product s₀ σ t hσ,
    LocalModelProduct.finiteFourier_claim.spectral_product s₀ σ t hσ]

/-- Absolute integrability of the exact spectral integrand in the paper's Poisson lemma. -/
theorem integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (integrand s₀ σ) := by
  simp_rw [show integrand s₀ σ = fun t => ArchimedeanFourier.fourier s₀ σ t *
      CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier
        LocalModelProduct.family s₀ σ t from funext fun t => integrand_eq_coordinate s₀ σ t h₀ hσ]
  exact SpectralIntegrand.integrable_local_product s₀ σ h₀ hσ

end Cubic.PoissonSummation.AdelicSpectralIntegrand
