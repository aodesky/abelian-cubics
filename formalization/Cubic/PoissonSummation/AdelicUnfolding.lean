import Cubic.PoissonSummation.AdelicPrincipalizationConsequences
import Cubic.PoissonSummation.AdelicLevelInvariance
import Cubic.PoissonSummation.AdelicPeriodization
import Cubic.PoissonSummation.AdelicSpatialIntegrability
import CubicTargets.PoissonSummation.AdelicPeriodizationConvergence

/-!
# Counting-measure unfolding of the actual height

Mathlib's nonnegative fundamental-domain integration theorem supplies the sum
over the rational diagonal. Compact-level invariance and the proved coordinate
measure of the representative region then give the factor `1/6`.

Every theorem requiring the region to cover retains an explicit
`FinitePrincipalization` premise. `PrimePrincipalization.finitePrincipalization`
discharges it in `AdelicPeriodizationConvergence`.
No Poisson formula is used.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicUnfolding

open MeasureTheory Set
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicCompactQuotient AdelicLevel AdelicHeightZetaData
open AdelicPrincipalizationConsequences
open CubicTargets.PoissonSummation.LogarithmExactSequence
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology ENNReal

/-- The diagonal identifies the paper's indexing group with its actual subgroup of the adeles. -/
def diagonalEquiv : RationalPoints ≃ RationalAdelicEmbedding.diagonal.range :=
  Equiv.ofInjective _ RationalAdelicEmbedding.diagonal_injective

def normPeriodization (s₀ σ : ℂ) (x : AdelicData.Points) : ℝ≥0∞ :=
  ∑' γ : RationalPoints, ‖cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * x)‖ₑ

def radialNormPeriodization (s₀ σ : ℂ) (u : ℝ) : ℝ≥0∞ :=
  ∑' γ : RationalPoints, ‖periodizationTerm s₀ σ γ u‖ₑ

theorem measurable_normPeriodization (s₀ σ : ℂ) : Measurable (normPeriodization s₀ σ) :=
  Measurable.ennreal_tsum fun _ =>
    ((measurable_cutoffHeight s₀ σ).comp (measurable_const.mul measurable_id)).enorm

theorem measurable_radialNormPeriodization (s₀ σ : ℂ) :
    Measurable (radialNormPeriodization s₀ σ) :=
  Measurable.ennreal_tsum fun γ =>
    (AdelicPeriodization.continuous_periodizationTerm s₀ σ γ).measurable.enorm

theorem realCoordinate_radial_mul_level (u : ℝ) (k : level) :
    realCoordinate (AdelicData.radialSection u * k) = u := by
  unfold realCoordinate
  rw [map_mul, coordinate_eq_one_of_mem_maximalCompact (level_le_maximalCompact k.property),
    mul_one, coordinate_radialSection]
  rfl

theorem normPeriodization_on_representativeRegion (s₀ σ : ℂ) {x : AdelicData.Points}
    (hx : x ∈ representativeRegion) :
    normPeriodization s₀ σ x = radialNormPeriodization s₀ σ (realCoordinate x) := by
  obtain ⟨u, k, rfl⟩ := (mem_representativeRegion_iff x).mp hx
  rw [realCoordinate_radial_mul_level]
  apply tsum_congr
  intro γ
  rw [← mul_assoc, cutoffHeight_mul_level s₀ σ _ _ k.property]
  rfl

/-- Counting on the rational diagonal is the sum in the fundamental-domain formula. -/
theorem lintegral_eq_region_normPeriodization (h : FinitePrincipalization) (s₀ σ : ℂ) :
    (∫⁻ x, ‖cutoffHeight s₀ σ x‖ₑ ∂measure) =
      ∫⁻ x in representativeRegion, normPeriodization s₀ σ x ∂measure := by
  rw [(fundamentalDomain_of_finitePrincipalization h).lintegral_eq_tsum'']
  have hm (γ : RationalAdelicEmbedding.diagonal.range) :
      AEMeasurable (fun x => ‖cutoffHeight s₀ σ (γ • x)‖ₑ)
        (measure.restrict representativeRegion) := by
    change AEMeasurable (fun x => ‖cutoffHeight s₀ σ ((γ : AdelicData.Points) * x)‖ₑ) _
    exact (((measurable_cutoffHeight s₀ σ).comp
      (measurable_const.mul measurable_id)).enorm).aemeasurable
  rw [← lintegral_tsum hm]
  apply lintegral_congr
  intro x
  exact (diagonalEquiv.tsum_eq
    (fun γ => ‖cutoffHeight s₀ σ ((γ : AdelicData.Points) * x)‖ₑ)).symm

/-- The paper's unfolding identity, with normalization derived from the actual Haar measure. -/
theorem lintegral_norm_eq_radial (h : FinitePrincipalization) (s₀ σ : ℂ) :
    (∫⁻ x, ‖cutoffHeight s₀ σ x‖ₑ ∂measure) =
      (1 / 6 : ℝ≥0∞) * ∫⁻ u : ℝ, radialNormPeriodization s₀ σ u := by
  rw [lintegral_eq_region_normPeriodization h]
  calc
    (∫⁻ x in representativeRegion, normPeriodization s₀ σ x ∂measure) =
        ∫⁻ x in representativeRegion, radialNormPeriodization s₀ σ (realCoordinate x) ∂measure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_representativeRegion.measurableSet] with x hx
      exact normPeriodization_on_representativeRegion s₀ σ hx
    _ = ∫⁻ u, radialNormPeriodization s₀ σ u
        ∂((measure.restrict representativeRegion).map realCoordinate) :=
      (lintegral_map (measurable_radialNormPeriodization s₀ σ)
        (show Continuous realCoordinate from AdelicCompactQuotient.continuous_coordinate).measurable).symm
    _ = _ := by rw [map_representativeRegion_coordinate, lintegral_smul_measure, smul_eq_mul]

/-- Tonelli and spatial integrability provide the summable base point used by the paper. -/
theorem exists_summable_at (h : FinitePrincipalization) (s₀ σ : ℂ)
    (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    ∃ u : ℝ, Summable (fun γ : RationalPoints => ‖periodizationTerm s₀ σ γ u‖) := by
  have hi := (AdelicSpatialIntegrability.spatial_integrable s₀ σ h₀ hσ).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm, lintegral_norm_eq_radial h s₀ σ] at hi
  have hf : (∫⁻ u : ℝ, radialNormPeriodization s₀ σ u) ≠ ⊤ := by
    intro ht
    rw [ht, ENNReal.mul_top (by norm_num : (1 / 6 : ℝ≥0∞) ≠ 0)] at hi
    exact hi.false
  obtain ⟨u, hu⟩ := (ae_lt_top (measurable_radialNormPeriodization s₀ σ) hf).exists
  refine ⟨u, ?_⟩
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hu.ne

/-- Assemble the supporting spatial and periodization conclusions. -/
theorem convergence_of_finitePrincipalization (h : FinitePrincipalization) :
    CubicTargets.PoissonSummation.AdelicPeriodizationConvergence.Claim := by
  have hc (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
      (∀ u : ℝ, Summable (fun γ : RationalPoints => ‖periodizationTerm s₀ σ γ u‖)) ∧
      HasSumLocallyUniformly (periodizationTerm s₀ σ) (periodization s₀ σ) ∧
      Continuous (periodization s₀ σ) ∧
      Summable (fun γ : IntegralRationalPoints => ‖zetaTerm s₀ σ γ‖) := by
    obtain ⟨u, hu⟩ := exists_summable_at h s₀ σ h₀ hσ
    exact AdelicPeriodization.convergence_of_summable_at s₀ σ h₀ hσ u hu
  exact ⟨AdelicSpatialIntegrability.spatial_integrable,
    fun s₀ σ h₀ hσ => (hc s₀ σ h₀ hσ).1,
    fun s₀ σ h₀ hσ => (hc s₀ σ h₀ hσ).2.1,
    fun s₀ σ h₀ hσ => (hc s₀ σ h₀ hσ).2.2.1,
    fun s₀ σ h₀ hσ => (hc s₀ σ h₀ hσ).2.2.2⟩

end Cubic.PoissonSummation.AdelicUnfolding
