import Cubic.PoissonSummation.AdelicFourierUnfolding
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# From adelic almost-everywhere Poisson to evaluation at the identity

This is the last step of the paper's proof of `lemma:poissonIntegral`.
Dominated convergence makes the actual spectral integral continuous. An
ambient almost-everywhere equality is restricted to the genuine fundamental
region and pushed to its real coordinate of measure `du/6`; it is not
specialized to a measure-zero radial section. Equality of continuous functions
then gives evaluation at zero.

The normalized adelic almost-everywhere identity remains an explicit premise.
This module neither assumes that premise as an axiom nor derives it using
real Fourier inversion.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicPoissonEvaluation

open MeasureTheory Filter AdelicHeightZetaData AdelicLevel
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData ENNReal

/-- Reconstruction with the paper's positive character and spectral scalar six. -/
def reconstruction (s₀ σ : ℂ) (u : ℝ) : ℂ :=
  6 * ∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t *
    (Circle.exp (2 * Real.pi * t * u) : ℂ)

theorem reconstruction_continuous (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Continuous (reconstruction s₀ σ) := by
  have hf := AdelicSpectralIntegrand.integrable s₀ σ h₀ hσ
  apply continuous_const.mul
  apply continuous_of_dominated (bound := fun t => ‖AdelicSpectralIntegrand.integrand s₀ σ t‖)
  · intro u
    apply hf.aestronglyMeasurable.mul
    exact (continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro u
    filter_upwards with t
    simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]
  · exact hf.norm
  · filter_upwards with t
    exact continuous_const.mul (continuous_subtype_val.comp
      (Circle.exp.continuous.comp (by fun_prop)))

@[simp]
theorem reconstruction_zero (s₀ σ : ℂ) :
    reconstruction s₀ σ 0 = 6 * ∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t := by
  simp [reconstruction]

/-- Push the a.e. identity through a positive-measure fundamental region.
This is the measure-theoretic descent required before using continuity. -/
theorem radial_ae_of_adelic_ae (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re)
    (hAE : ∀ᵐ x ∂AdelicHeightZetaData.measure,
      (∑' γ : RationalPoints,
        cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
          reconstruction s₀ σ (realCoordinate x)) :
    periodization s₀ σ =ᵐ[volume] reconstruction s₀ σ := by
  have hregion : ∀ᵐ x ∂(AdelicHeightZetaData.measure.restrict representativeRegion),
      periodization s₀ σ (realCoordinate x) = reconstruction s₀ σ (realCoordinate x) := by
    filter_upwards [ae_restrict_of_ae hAE, ae_restrict_mem isOpen_representativeRegion.measurableSet]
      with x hx hmem
    rw [AdelicFourierUnfolding.periodization_on_region s₀ σ hmem] at hx
    exact hx
  have hmap : periodization s₀ σ =ᵐ[
      (AdelicHeightZetaData.measure.restrict representativeRegion).map realCoordinate]
        reconstruction s₀ σ := by
    have hm : Measurable realCoordinate :=
      (show Continuous realCoordinate from AdelicCompactQuotient.continuous_coordinate).measurable
    exact (ae_map_iff hm.aemeasurable (isClosed_eq
      (adelicPeriodizationConvergence.periodization_continuous s₀ σ h₀ hσ)
      (reconstruction_continuous s₀ σ h₀ hσ)).measurableSet).mpr hregion
  rw [map_representativeRegion_coordinate] at hmap
  exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 6 : ℝ≥0∞) ≠ 0)).mp hmap

/-- The paper's continuity argument promotes the adelic a.e. equality to the
height-series identity, without evaluating an a.e. statement at a point. -/
theorem equality_at_zero_of_adelic_ae (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re)
    (hAE : ∀ᵐ x ∂AdelicHeightZetaData.measure,
      (∑' γ : RationalPoints,
        cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
          reconstruction s₀ σ (realCoordinate x)) :
    heightZeta s₀ σ = 6 * ∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t := by
  have he := Measure.eq_of_ae_eq (radial_ae_of_adelic_ae s₀ σ h₀ hσ hAE)
    (adelicPeriodizationConvergence.periodization_continuous s₀ σ h₀ hσ)
    (reconstruction_continuous s₀ σ h₀ hσ)
  simpa only [AdelicPeriodization.periodization_zero, reconstruction_zero] using congrFun he 0

end Cubic.PoissonSummation.AdelicPoissonEvaluation
