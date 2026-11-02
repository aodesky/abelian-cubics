import Cubic.PoissonSummation.AdelicFourierIntegral
import Cubic.PoissonSummation.AdelicPeriodizationConvergence
import Cubic.PoissonSummation.RealFourierInversion

/-!
# Fourier unfolding with the original counting normalization

Unfold an integrable function over the proved rational fundamental domain.
For the cutoff height times an inverse automorphic character, the product
formula removes the character of each rational point. Level invariance and
the actual coordinate pushforward then identify the global Fourier integral
with one sixth of the real Fourier transform of the original periodization.
This is an identity of independently defined functions, not a spectral assumption.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierUnfolding

open MeasureTheory Set
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicHeightZetaData AdelicLevel AdelicCompactQuotient
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology ENNReal
  FourierTransform

/-- Complex counting-measure unfolding; integrability justifies exchanging sum and integral. -/
theorem integral_eq_region_tsum (f : Points → ℂ) (hm : Measurable f)
    (hi : Integrable f AdelicHeightZetaData.measure) :
    (∫ x, f x ∂AdelicHeightZetaData.measure) = ∫ x in representativeRegion,
      ∑' γ : RationalPoints, f (RationalAdelicEmbedding.diagonal γ * x)
        ∂AdelicHeightZetaData.measure := by
  rw [AdelicQuotientMeasure.fundamentalDomain.integral_eq_tsum'' f hi]
  change (∑' γ : RationalAdelicEmbedding.diagonal.range,
    ∫ x in representativeRegion, f ((γ : Points) * x) ∂AdelicHeightZetaData.measure) = _
  have hmeas (γ : RationalAdelicEmbedding.diagonal.range) :
      AEStronglyMeasurable (fun x : Points => f ((γ : Points) * x))
        (AdelicHeightZetaData.measure.restrict representativeRegion) :=
    (hm.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hfinite : (∑' γ : RationalAdelicEmbedding.diagonal.range,
      ∫⁻ x in representativeRegion, ‖f ((γ : Points) * x)‖ₑ
        ∂AdelicHeightZetaData.measure) ≠ ∞ := by
    have he := AdelicQuotientMeasure.fundamentalDomain.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    change (∫⁻ x, ‖f x‖ₑ ∂AdelicHeightZetaData.measure) =
      (∑' γ : RationalAdelicEmbedding.diagonal.range,
        ∫⁻ x in representativeRegion, ‖f ((γ : Points) * x)‖ₑ
          ∂AdelicHeightZetaData.measure) at he
    rw [← he]
    exact hi.hasFiniteIntegral.ne
  rw [← integral_tsum hmeas hfinite]
  apply integral_congr_ae
  filter_upwards with x
  exact (AdelicUnfolding.diagonalEquiv.tsum_eq _).symm

theorem character_eq_coordinate (t : ℝ) (x : Points) :
    AdelicData.character t x = Circle.exp (2 * Real.pi * t * realCoordinate x) := by
  rw [AdelicData.character_apply]
  congr 1
  simp only [LocalLogarithmNormalization.spectralPairing,
    ← AdelicData.logarithm_invariant, realCoordinate, coordinate]
  dsimp
  ring

theorem measurable_integrand (s₀ σ : ℂ) (t : ℝ) :
    Measurable (AdelicFourierIntegral.integrand s₀ σ t) := by
  apply (measurable_cutoffHeight s₀ σ).mul
  exact (continuous_subtype_val.comp (AdelicData.character t).continuous).measurable.inv

theorem rational_translate_integrand (s₀ σ : ℂ) (t : ℝ) (γ : RationalPoints) (x : Points) :
    AdelicFourierIntegral.integrand s₀ σ t (RationalAdelicEmbedding.diagonal γ * x) =
      cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x) *
        ((AdelicData.character t x : Circle) : ℂ)⁻¹ := by
  simp only [AdelicFourierIntegral.integrand, AdelicRationalCharacter.automorphicCharacter_mk,
    map_mul, AdelicRationalCharacter.character_diagonal, one_mul]

theorem periodization_on_region (s₀ σ : ℂ) {x : Points} (hx : x ∈ representativeRegion) :
    (∑' γ : RationalPoints, cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)) =
      periodization s₀ σ (realCoordinate x) := by
  obtain ⟨u, k, rfl⟩ := (mem_representativeRegion_iff x).mp hx
  rw [AdelicUnfolding.realCoordinate_radial_mul_level]
  apply tsum_congr
  intro γ
  rw [← mul_assoc, cutoffHeight_mul_level s₀ σ _ _ k.property]
  rfl

/-- The original radial periodization is in `L¹(du)`, using the actual unfolding estimate. -/
theorem periodization_integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (periodization s₀ σ) := by
  refine ⟨(adelicPeriodizationConvergence.periodization_continuous s₀ σ h₀ hσ).aestronglyMeasurable,
    ?_⟩
  have hi := (AdelicSpatialIntegrability.spatial_integrable s₀ σ h₀ hσ).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm,
    AdelicUnfolding.lintegral_norm_eq_radial PrimePrincipalization.finitePrincipalization s₀ σ] at hi
  have hf : (∫⁻ u : ℝ, AdelicUnfolding.radialNormPeriodization s₀ σ u) < ∞ := by
    by_contra h
    have he := not_lt_top_iff.mp h
    rw [he, ENNReal.mul_top (by norm_num : (1 / 6 : ℝ≥0∞) ≠ 0)] at hi
    exact hi.false
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_mono (fun u => enorm_tsum_le_tsum_enorm)).trans_lt hf

/-- The global transform and the real periodization use reciprocal measure scalars. -/
theorem fourier_eq_radial (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    AdelicFourierIntegral.fourier s₀ σ t = (1 / 6 : ℂ) * 𝓕 (periodization s₀ σ) t := by
  let g : ℝ → ℂ := fun u => periodization s₀ σ u * (Circle.exp (2 * Real.pi * t * u) : ℂ)⁻¹
  have hg : Continuous g := by
    apply (adelicPeriodizationConvergence.periodization_continuous s₀ σ h₀ hσ).mul
    simp only [Circle.coe_exp, ← Complex.exp_neg]
    fun_prop
  rw [AdelicFourierIntegral.fourier, integral_eq_region_tsum _ (measurable_integrand s₀ σ t)
    (AdelicFourierIntegral.integrable s₀ σ t h₀ hσ)]
  calc
    (∫ x in representativeRegion, ∑' γ : RationalPoints,
        AdelicFourierIntegral.integrand s₀ σ t (RationalAdelicEmbedding.diagonal γ * x)
          ∂AdelicHeightZetaData.measure) =
        ∫ x in representativeRegion, g (realCoordinate x) ∂AdelicHeightZetaData.measure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_representativeRegion.measurableSet] with x hx
      simp_rw [rational_translate_integrand, tsum_mul_right,
        periodization_on_region s₀ σ hx, character_eq_coordinate]
      rfl
    _ = ∫ u, g u ∂((AdelicHeightZetaData.measure.restrict representativeRegion).map
        realCoordinate) :=
      (integral_map (show Continuous realCoordinate from continuous_coordinate).measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = (1 / 6 : ℂ) * ∫ u, g u := by
      rw [map_representativeRegion_coordinate, integral_smul_measure]
      norm_num [smul_eq_mul]
    _ = _ := by
      congr 1
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with u
      simp only [g, Circle.coe_exp, ← Complex.exp_neg, smul_eq_mul, RCLike.inner_apply,
        conj_trivial]
      rw [mul_comm]
      congr 2
      push_cast
      ring

end Cubic.PoissonSummation.AdelicFourierUnfolding
