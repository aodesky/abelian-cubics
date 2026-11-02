import Cubic.PoissonSummation.AdelicQuotientMeasure
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Haar properties of the actual counting-normalized quotient measure

The measure is the previously constructed fundamental-domain pushforward.
Its real coordinate still has measure `du/6`. Here we verify the topological
and measure-class hypotheses needed to instantiate the general Poisson input.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicQuotientMeasure

open MeasureTheory TopologicalSpace Set Filter
open AdelicRationalCharacter RationalAdelicEmbedding AdelicLevel
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology
  Topology Uniformity Pointwise ENNReal

private theorem polish_of_locallyCompact (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] :
    PolishSpace G := by
  letI := IsTopologicalGroup.rightUniformSpace G
  letI : IsUniformGroup G := isUniformGroup_of_commGroup
  letI : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  letI : (𝓤 G).IsCountablyGenerated := IsUniformGroup.uniformity_countably_generated
  infer_instance

scoped instance : PolishSpace AdelicData.Points := polish_of_locallyCompact _

scoped instance : IsClosed (diagonal.range : Set AdelicData.Points) :=
  Subgroup.isClosed_of_discrete

open scoped AdelicQuotientMeasure

scoped instance : T3Space AutomorphicQuotient := QuotientGroup.instT3Space _
scoped instance : T2Space AutomorphicQuotient :=
  @T25Space.t2Space AutomorphicQuotient _ T3Space.t25Space
scoped instance : BorelSpace AutomorphicQuotient := QuotientGroup.borelSpace
scoped instance : PolishSpace AutomorphicQuotient := polish_of_locallyCompact _
scoped instance : MetrizableSpace AutomorphicQuotient := IsCompletelyMetrizableSpace.MetrizableSpace
scoped instance : SigmaCompactSpace AutomorphicQuotient :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-- Mathlib's quotient-measure interface uses the right action. Commutativity
identifies it with the left action of our existing fundamental-domain proof. -/
theorem fundamentalDomain_op :
    IsFundamentalDomain diagonal.range.op representativeRegion AdelicHeightZetaData.measure := by
  let e := diagonal.range.equivOp
  have ha (g : diagonal.range.op) (x : AdelicData.Points) :
      g • x = (e.symm g : AdelicData.Points) * x := mul_comm _ _
  have hs (g : diagonal.range.op) : g • representativeRegion =
      e.symm g • representativeRegion := by
    change (fun x => g • x) '' representativeRegion =
      (fun x => (e.symm g : AdelicData.Points) * x) '' representativeRegion
    simp only [ha]
  refine ⟨fundamentalDomain.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [fundamentalDomain.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨e g, by simpa only [ha, e.symm_apply_apply] using hg⟩
  · intro g h hne
    change AEDisjoint AdelicHeightZetaData.measure (g • representativeRegion)
      (h • representativeRegion)
    rw [hs, hs]
    exact fundamentalDomain.aedisjoint (fun he => hne (e.symm.injective he))

scoped instance : HasFundamentalDomain diagonal.range.op AdelicData.Points
    AdelicHeightZetaData.measure := ⟨representativeRegion, fundamentalDomain_op⟩

scoped instance : QuotientMeasureEqMeasurePreimage AdelicHeightZetaData.measure quotientMeasure :=
  fundamentalDomain_op.quotientMeasureEqMeasurePreimage_quotientMeasure

instance : quotientMeasure.IsMulLeftInvariant :=
  QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient AdelicHeightZetaData.measure

/-- Every compact set has finite measure, bounded by its compact real-coordinate image. -/
instance : IsFiniteMeasureOnCompacts quotientMeasure where
  lt_top_of_isCompact K hK := by
    have hc : Continuous quotientRealCoordinate := AdelicCompactQuotient.continuous_quotientCoordinate
    have hi := hK.image hc
    have hm : MeasurableSet (quotientRealCoordinate '' K) := hi.measurableSet
    have hle : quotientMeasure K ≤
        (quotientMeasure.map quotientRealCoordinate) (quotientRealCoordinate '' K) := by
      rw [Measure.map_apply measurable_quotientRealCoordinate hm]
      exact measure_mono (subset_preimage_image _ _)
    rw [map_quotientMeasure_coordinate] at hle
    exact hle.trans_lt (by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (by norm_num) hi.measure_lt_top)

instance : quotientMeasure.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance : NeZero quotientMeasure := by
  constructor
  intro he
  have hm := map_quotientMeasure_coordinate
  rw [he, Measure.map_zero] at hm
  have hi := congrArg (fun μ : Measure ℝ => μ (Icc 0 1)) hm
  norm_num [Measure.smul_apply] at hi
  exact (by norm_num : (6 : ℝ≥0∞)⁻¹ ≠ 0) hi.symm

instance : quotientMeasure.IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsMulLeftInvariant := inferInstance
  toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular

end Cubic.PoissonSummation.AdelicQuotientMeasure
