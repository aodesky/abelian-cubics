import Cubic.PoissonSummation.PoissonAdelicApplication
import CubicTargets.PoissonSummation.PoissonWithDualMeasure

/-!
# `lemma:poissonIntegral`: the paper's adelic Poisson application

The only general analytic input is the Poisson summation input `PoissonWithDualMeasure.BlackBox`,
including existence of the Fourier-normalized full dual Haar measure.
All cubic-specific data and hypotheses are proved: spatial and full-dual
integrability, spectral support and factorization, the measure scalar six,
counting normalization, and evaluation at the identity by continuity.
-/

namespace Cubic.PoissonSummation

open MeasureTheory AdelicHeightZetaData AdelicQuotientMeasure
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology
  AdelicQuotientMeasure AdelicFourierSpectrum

/-- The full paper lemma, relative only to the assumed general
Poisson and normalized-dual existence input. -/
theorem «lemma:poissonIntegral»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.PoissonIntegral.Claim := by
  obtain ⟨ν, hHaar, hRegular, hInv, hPS⟩ :=
    hPoisson AdelicData.Points RationalAdelicEmbedding.diagonal.range
      AdelicHeightZetaData.measure quotientMeasure
  letI := hHaar
  letI := hRegular
  refine
    { series_absolute := adelicPeriodizationConvergence.zeta_absolute
      spectral_integrable := AdelicSpectralIntegrand.integrable
      poisson_equality := fun s₀ σ h₀ hσ => ?_ }
  have hAE := hPS (cutoffHeight s₀ σ)
    (AdelicSpatialIntegrability.spatial_integrable s₀ σ h₀ hσ)
    (PoissonAdelicApplication.transform_integrable ν s₀ σ h₀ hσ)
  exact AdelicPoissonEvaluation.equality_at_zero_of_adelic_ae s₀ σ h₀ hσ
    (PoissonAdelicApplication.normalize_adelic_ae ν hInv s₀ σ hσ hAE)

end Cubic.PoissonSummation
