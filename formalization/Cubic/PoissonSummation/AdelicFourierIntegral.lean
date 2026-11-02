import Cubic.PoissonSummation.FiniteAdelicFourierIntegral
import Cubic.PoissonSummation.AdelicSpectralIntegrand

/-!
# The actual adelic Fourier integral factors into local integrals

Keep the original cutoff height, descended automorphic character and Haar
measure in the definition. Finite-place exhaustion and the product measure
then give the spectral integrand of `lemma:poissonIntegral`. In particular,
the factor at three and the inverse-character convention are inherited from
the original local integrals, not imposed on the global transform.

This factorization is not a Poisson formula: identifying the dual measure and
relating the integral to rational-point periodization are done in the files proving `lemma:poissonIntegral`.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierIntegral

open MeasureTheory
open AdelicHeightZetaData
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData

/-- Fourier integrand on the original adelic group, with inverse automorphic character. -/
def integrand (s₀ σ : ℂ) (t : ℝ) (x : Points) : ℂ :=
  cutoffHeight s₀ σ x *
    ((AdelicRationalCharacter.automorphicCharacter t (QuotientGroup.mk x) : Circle) : ℂ)⁻¹

/-- The actual global Fourier integral, independently of the local product formula. -/
def fourier (s₀ σ : ℂ) (t : ℝ) : ℂ := ∫ x, integrand s₀ σ t x ∂measure

theorem integrand_eq_components (s₀ σ : ℂ) (t : ℝ) (x : Points) :
    integrand s₀ σ t x = ArchimedeanHaarData.integrand s₀ σ t x.1 *
      FiniteAdelicFourierIntegral.integrand s₀ σ t x.2 := by
  simp only [integrand, cutoffHeight_eq_components, ArchimedeanHaarData.integrand,
    AdelicRationalCharacter.automorphicCharacter_mk,
    AdelicData.inverseHeight_includeInfinite, AdelicData.character_includeInfinite,
    FiniteAdelicFourierIntegral.integrand]
  rw [AdelicData.character_eq_components, Circle.coe_mul, mul_inv]
  ring

theorem integrable (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (integrand s₀ σ t) measure := by
  have h := (ArchimedeanTorusFourier.integrable _ ArchimedeanHaar.normalized s₀ σ t h₀
    (lt_trans zero_lt_one hσ)).mul_prod (FiniteAdelicFourierIntegral.integrable s₀ σ t hσ)
  simpa only [← integrand_eq_components, AdelicHeightZetaData.measure] using h

/-- Global Fourier factorization for the actual height, with no extra normalization scalar. -/
theorem fourier_eq_local_product (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    fourier s₀ σ t = AdelicSpectralIntegrand.integrand s₀ σ t := by
  simp_rw [fourier, integrand_eq_components]
  rw [AdelicHeightZetaData.measure, integral_prod_mul,
    FiniteAdelicFourierIntegral.integral_eq_product s₀ σ t hσ]
  rw [AdelicSpectralIntegrand.integrand, AdelicFourierComponents.finiteFourier_eq]
  rfl

/-- The spatial Fourier transform is integrable in the spectral parameter. -/
theorem fourier_integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (fourier s₀ σ) := by
  simp_rw [show fourier s₀ σ = AdelicSpectralIntegrand.integrand s₀ σ from
    funext fun t => fourier_eq_local_product s₀ σ t hσ]
  exact AdelicSpectralIntegrand.integrable s₀ σ h₀ hσ

end Cubic.PoissonSummation.AdelicFourierIntegral
