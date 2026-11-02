import Cubic.PoissonSummation.PrimePrincipalization
import Cubic.PoissonSummation.AdelicUnfolding

/-!
# The actual counting-normalized adelic quotient measure

Finite principalization makes `a(ℝ)K^{D₀}` a genuine fundamental domain.
Push the restricted Haar measure to the rational quotient and verify its
counting-measure unfolding identity for every measurable nonnegative function.
The real logarithmic coordinate has pushforward `du/6`.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicQuotientMeasure

open MeasureTheory Set
open Cubic.QuadraticCorrespondence
open AdelicHeightZetaData AdelicLevel AdelicCompactQuotient
open AdelicRationalCharacter RationalAdelicEmbedding
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology ENNReal

theorem fundamentalDomain : IsFundamentalDomain diagonal.range representativeRegion measure :=
  AdelicPrincipalizationConsequences.fundamentalDomain_of_finitePrincipalization
    PrimePrincipalization.finitePrincipalization

/-- Defined using the actual fundamental region, then verified to use counting on rational points. -/
def quotientMeasure : Measure AutomorphicQuotient :=
  (measure.restrict representativeRegion).map QuotientGroup.mk

def quotientRealCoordinate (x : AutomorphicQuotient) : ℝ := (quotientCoordinate x).toAdd

theorem measurable_quotientRealCoordinate : Measurable quotientRealCoordinate := by
  apply QuotientGroup.measurable_from_quotient.mpr
  exact (show Continuous realCoordinate from AdelicCompactQuotient.continuous_coordinate).measurable

/-- This is the paper's measure on the real coordinate, with the scalar fixed by Haar normalization. -/
theorem map_quotientMeasure_coordinate :
    quotientMeasure.map quotientRealCoordinate = (1 / 6 : ℝ≥0∞) • volume := by
  rw [quotientMeasure, Measure.map_map measurable_quotientRealCoordinate
    QuotientGroup.measurable_coe]
  exact map_representativeRegion_coordinate

theorem automorphize_mk (f : AdelicData.Points → ℝ≥0∞) (x : AdelicData.Points) :
    QuotientGroup.automorphize f (QuotientGroup.mk x : AutomorphicQuotient) =
      ∑' γ : diagonal.range, f ((γ : AdelicData.Points) * x) := by
  change (∑' γ : diagonal.range.op, f (γ • x)) = _
  rw [← diagonal.range.equivOp.tsum_eq]
  apply tsum_congr
  intro γ
  exact congrArg f (mul_comm x (γ : AdelicData.Points))

theorem measurable_automorphize {f : AdelicData.Points → ℝ≥0∞} (hf : Measurable f) :
    Measurable (QuotientGroup.automorphize f : AutomorphicQuotient → ℝ≥0∞) := by
  apply QuotientGroup.measurable_from_quotient.mpr
  change Measurable (fun x : AdelicData.Points =>
    QuotientGroup.automorphize f (QuotientGroup.mk x : AutomorphicQuotient))
  simp_rw [automorphize_mk]
  exact Measurable.ennreal_tsum (fun _ => hf.comp (measurable_const.mul measurable_id))

/-- The normalization is counting measure on the rational subgroup, not probability on torsion. -/
theorem lintegral_unfold {f : AdelicData.Points → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂measure) =
      ∫⁻ x : AutomorphicQuotient, QuotientGroup.automorphize f x ∂quotientMeasure := by
  rw [quotientMeasure, lintegral_map (measurable_automorphize hf) QuotientGroup.measurable_coe]
  simp_rw [automorphize_mk]
  have hm (γ : diagonal.range) : AEMeasurable (fun x => f ((γ : AdelicData.Points) * x))
      (measure.restrict representativeRegion) :=
    (hf.comp (measurable_const.mul measurable_id)).aemeasurable
  rw [lintegral_tsum hm]
  exact fundamentalDomain.lintegral_eq_tsum'' f

/-- Reindex the automorphic sum by the original rational point group. -/
theorem automorphize_norm_mk (s₀ σ : ℂ) (x : AdelicData.Points) :
    QuotientGroup.automorphize (fun y => ‖cutoffHeight s₀ σ y‖ₑ)
      (QuotientGroup.mk x : AutomorphicQuotient) = AdelicUnfolding.normPeriodization s₀ σ x := by
  rw [automorphize_mk]
  exact (AdelicUnfolding.diagonalEquiv.tsum_eq _).symm

end Cubic.PoissonSummation.AdelicQuotientMeasure
