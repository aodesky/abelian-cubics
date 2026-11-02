import Cubic.PoissonSummation.AdelicCutoff
import Cubic.PoissonSummation.PeriodizationConvergence

/-!
# Actual summands in the height periodization

Identify the rational-point summands with the translated archimedean heights
used in the paper's comparison estimate. The finite factor is independent of
the real translation. Convergence at a base point is still to be supplied by
the quotient-unfolding argument; it is an explicit premise below.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicPeriodization

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicHeightZetaData RationalAdelicEmbedding
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  AdelicHeightZetaData

def finiteFactor (s₀ σ : ℂ) (γ : RationalPoints) : ℂ :=
  finiteCutoffHeight s₀ σ (finiteDiagonal γ)

def shift (γ : RationalPoints) : ℝ :=
  ArchimedeanQuotientLogarithm.coordinate (baseChange ℝ γ)

/-- The paper's `cγ` and `rγ` description on the actual rational-point summation domain. -/
theorem periodizationTerm_eq (s₀ σ : ℂ) (γ : RationalPoints) (u : ℝ) :
    periodizationTerm s₀ σ γ u =
      finiteFactor s₀ σ γ * ArchimedeanFourier.inverseHeight s₀ σ (shift γ + u) := by
  rw [periodizationTerm, cutoffHeight_eq_components]
  simp only [diagonal, MonoidHom.prod_apply, AdelicData.radialSection, AdelicData.includeInfinite,
    Prod.fst_mul, Prod.snd_mul, mul_one, ArchimedeanQuotientLogarithm.inverseHeight_eq,
    ArchimedeanQuotientLogarithm.coordinate_mul,
    ArchimedeanQuotientLogarithm.coordinate_radialSection]
  exact mul_comm _ _

theorem continuous_periodizationTerm (s₀ σ : ℂ) (γ : RationalPoints) :
    Continuous (periodizationTerm s₀ σ γ) := by
  change Continuous (fun u => periodizationTerm s₀ σ γ u)
  simp_rw [periodizationTerm_eq]
  exact continuous_const.mul ((ArchimedeanFourier.continuous_inverseHeight s₀ σ).comp
    (continuous_const.add continuous_id))

/-- The comparison holds for each actual summand before any summability assumption. -/
theorem norm_periodizationTerm_le (s₀ σ : ℂ) (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re)
    (γ : RationalPoints) (u v : ℝ) :
    ‖periodizationTerm s₀ σ γ u‖ ≤
      Real.exp (max s₀.re (2 * σ.re) * |u - v|) * ‖periodizationTerm s₀ σ γ v‖ := by
  simp only [periodizationTerm_eq]
  exact ArchimedeanFourier.norm_mul_inverseHeight_translate_le s₀ σ h₀ hσ
    (finiteFactor s₀ σ γ) (shift γ) u v

theorem radialSection_zero : AdelicData.radialSection 0 = 1 := by
  change (ArchimedeanQuotientLogarithm.radialSection 0, 1) = (1, 1)
  congr 1
  apply CyclotomicArchimedean.pointEquiv.injective
  simp [ArchimedeanQuotientLogarithm.radialSection]

theorem periodizationTerm_zero_eq_zetaTerm (s₀ σ : ℂ) (γ : IntegralRationalPoints) :
    periodizationTerm s₀ σ γ.1 0 = zetaTerm s₀ σ γ := by
  rw [periodizationTerm, radialSection_zero, mul_one, cutoffHeight,
    Set.indicator_of_mem γ.property, AdelicHeightLaws.inverseHeight_eq_reciprocal]
  rfl

/-- At the identity the original periodization is exactly the original height series. -/
theorem periodization_zero (s₀ σ : ℂ) : periodization s₀ σ 0 = heightZeta s₀ σ := by
  have hs : Function.support (fun γ : RationalPoints => periodizationTerm s₀ σ γ 0) ⊆
      {γ | RationalAdelicEmbedding.diagonal γ ∈ integralLocus} := by
    intro γ hγ
    by_contra hn
    change RationalAdelicEmbedding.diagonal γ ∉ integralLocus at hn
    apply hγ
    change periodizationTerm s₀ σ γ 0 = 0
    rw [periodizationTerm, radialSection_zero, mul_one,
      cutoffHeight, Set.indicator_of_notMem hn]
  change (∑' γ : RationalPoints, periodizationTerm s₀ σ γ 0) = ∑' γ : IntegralRationalPoints,
    zetaTerm s₀ σ γ
  rw [← tsum_subtype_eq_of_support_subset hs]
  exact tsum_congr fun γ => periodizationTerm_zero_eq_zetaTerm s₀ σ γ

/-- All remaining convergence conclusions follow once unfolding supplies one summable value. -/
theorem convergence_of_summable_at (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re)
    (u₀ : ℝ) (hsum : Summable (fun γ : RationalPoints => ‖periodizationTerm s₀ σ γ u₀‖)) :
    (∀ u : ℝ, Summable (fun γ : RationalPoints => ‖periodizationTerm s₀ σ γ u‖)) ∧
    HasSumLocallyUniformly (periodizationTerm s₀ σ) (periodization s₀ σ) ∧
    Continuous (periodization s₀ σ) ∧
    Summable (fun γ : IntegralRationalPoints => ‖zetaTerm s₀ σ γ‖) := by
  have h := PeriodizationConvergence.translated_height_series s₀ σ h₀.le
    (le_trans zero_le_one hσ.le) (finiteFactor s₀ σ) shift u₀
    (by simpa only [← periodizationTerm_eq] using hsum)
  simp only [← periodizationTerm_eq] at h
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  have hz := (h.1 0).subtype (fun γ => diagonal γ ∈ integralLocus)
  change Summable (fun γ : IntegralRationalPoints => ‖periodizationTerm s₀ σ γ.1 0‖) at hz
  simpa only [periodizationTerm_zero_eq_zetaTerm] using hz

end Cubic.PoissonSummation.AdelicPeriodization
