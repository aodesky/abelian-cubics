import Cubic.PoissonSummation.AdelicDualNormalization
import Cubic.PoissonSummation.AdelicPoissonEvaluation
import CubicTargets.PoissonSummation.PoissonAE
import CubicTargets.PoissonSummation.PoissonIntegral

/-!
# Applying general adelic Poisson to the original height

This follows the paper's route for `lemma:poissonIntegral`: apply general
Poisson on the original adelic group and its rational diagonal, restrict the
actual automorphic dual integral to the level annihilator, determine its Haar
scalar from quotient inversion, and use continuity to evaluate at the identity.

The helpers keep a full dual Haar measure and quotient inversion explicit.
The final paper proof in `PoissonIntegral` supplies them from the assumed
`PoissonWithDualMeasure.BlackBox`. The earlier supplied-measure form is retained
here as a conditional helper.
-/

noncomputable section

namespace Cubic.PoissonSummation.PoissonAdelicApplication

open MeasureTheory Filter
open AdelicHeightZetaData AdelicRationalCharacter AdelicQuotientMeasure AdelicFourierSpectrum
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology
  AdelicQuotientMeasure AdelicFourierSpectrum ENNReal NNReal

theorem transform_support (s₀ σ : ℂ) :
    Function.support (transform s₀ σ) ⊆ levelAnnihilator :=
  fun χ hχ => quotientLevel_le_ker_of_nonzero s₀ σ χ hχ

/-- The second Poisson hypothesis is proved on the entire actual automorphic dual. -/
theorem transform_integrable (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (transform s₀ σ) ν := by
  rw [integrable_iff_coordinate ν _ (transform_support s₀ σ)]
  exact AdelicFourierIntegral.fourier_integrable s₀ σ h₀ hσ

variable (ν : Measure (PontryaginDual AutomorphicQuotient)) [ν.IsHaarMeasure]
  (hInv : ∀ F : AutomorphicQuotient → ℂ,
    let Fhat := fun χ : PontryaginDual AutomorphicQuotient =>
      ∫ q, F q * (χ q : ℂ)⁻¹ ∂quotientMeasure
    Integrable F quotientMeasure → Integrable Fhat ν →
      ∀ᵐ q ∂quotientMeasure, F q = ∫ χ, Fhat χ * (χ q : ℂ) ∂ν)

include hInv

/-- The actual full-dual reconstruction integral is the paper's real integral,
with the independently proved scalar six and positive reconstruction character. -/
theorem reconstruction_eq (s₀ σ : ℂ) (hσ : 1 < σ.re) (x : AdelicData.Points) :
    (∫ χ, transform s₀ σ χ * (χ (QuotientGroup.mk x) : ℂ) ∂ν) =
      AdelicPoissonEvaluation.reconstruction s₀ σ (AdelicLevel.realCoordinate x) := by
  have hsupp : Function.support (fun χ : PontryaginDual AutomorphicQuotient =>
      transform s₀ σ χ * (χ (QuotientGroup.mk x) : ℂ)) ⊆ levelAnnihilator :=
    fun χ hχ => transform_support s₀ σ (left_ne_zero_of_mul hχ)
  rw [integral_eq_scalar_mul ν _ hsupp, AdelicDualNormalization.spectralScalar_eq_six ν hInv]
  simp only [NNReal.coe_ofNat, Complex.ofReal_ofNat, transform_automorphicCharacter,
    AdelicFourierIntegral.fourier_eq_local_product s₀ σ _ hσ,
    automorphicCharacter_mk, AdelicFourierUnfolding.character_eq_coordinate]
  rfl

/-- Transfer the actual general-Poisson conclusion to the paper's normalized
real integral. Absolute convergence of its counting integral is retained. -/
theorem normalize_adelic_ae (s₀ σ : ℂ) (hσ : 1 < σ.re)
    (hAE : ∀ᵐ x ∂AdelicHeightZetaData.measure,
      Integrable (fun γ : RationalAdelicEmbedding.diagonal.range =>
        cutoffHeight s₀ σ ((γ : AdelicData.Points) * x)) Measure.count ∧
      (∫ γ : RationalAdelicEmbedding.diagonal.range,
        cutoffHeight s₀ σ ((γ : AdelicData.Points) * x) ∂Measure.count) =
        ∫ χ, transform s₀ σ χ * (χ (QuotientGroup.mk x) : ℂ) ∂ν) :
    ∀ᵐ x ∂AdelicHeightZetaData.measure,
      (∑' γ : RationalPoints,
        cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
          AdelicPoissonEvaluation.reconstruction s₀ σ (AdelicLevel.realCoordinate x) := by
  filter_upwards [hAE] with x hx
  have hc := integral_countable' hx.1
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] at hc
  calc
    (∑' γ : RationalPoints,
        cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
        ∑' γ : RationalAdelicEmbedding.diagonal.range,
          cutoffHeight s₀ σ ((γ : AdelicData.Points) * x) :=
      AdelicUnfolding.diagonalEquiv.tsum_eq
        (fun γ => cutoffHeight s₀ σ ((γ : AdelicData.Points) * x))
    _ = ∫ γ : RationalAdelicEmbedding.diagonal.range,
        cutoffHeight s₀ σ ((γ : AdelicData.Points) * x) ∂Measure.count := hc.symm
    _ = ∫ χ, transform s₀ σ χ * (χ (QuotientGroup.mk x) : ℂ) ∂ν := hx.2
    _ = _ := reconstruction_eq ν hInv s₀ σ hσ x

variable [ν.Regular]

/-- Invoke the existing general black box only after verifying both `L¹`
hypotheses and every actual quotient-measure obligation. -/
theorem adelic_ae (hPoisson : CubicTargets.PoissonSummation.PoissonAE.BlackBox)
    (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    ∀ᵐ x ∂AdelicHeightZetaData.measure,
      (∑' γ : RationalPoints,
        cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
          AdelicPoissonEvaluation.reconstruction s₀ σ (AdelicLevel.realCoordinate x) := by
  have h := hPoisson AdelicData.Points RationalAdelicEmbedding.diagonal.range
    AdelicHeightZetaData.measure quotientMeasure ν hInv (cutoffHeight s₀ σ)
    (AdelicSpatialIntegrability.spatial_integrable s₀ σ h₀ hσ)
    (transform_integrable ν s₀ σ h₀ hσ)
  exact normalize_adelic_ae ν hInv s₀ σ hσ h

/-- All conclusions of the concrete Poisson lemma, conditional on the existing
general Poisson input and existence of a Fourier-normalized full dual measure. -/
theorem claim_of_blackBox (hPoisson : CubicTargets.PoissonSummation.PoissonAE.BlackBox) :
    CubicTargets.PoissonSummation.PoissonIntegral.Claim where
  series_absolute := adelicPeriodizationConvergence.zeta_absolute
  spectral_integrable := AdelicSpectralIntegrand.integrable
  poisson_equality s₀ σ h₀ hσ :=
    AdelicPoissonEvaluation.equality_at_zero_of_adelic_ae s₀ σ h₀ hσ
      (adelic_ae ν hInv hPoisson s₀ σ h₀ hσ)

end Cubic.PoissonSummation.PoissonAdelicApplication
