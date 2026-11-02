import Cubic.PoissonSummation.ArchimedeanHaarData
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Haar normalization on the original real torus

Compact logarithmic bands make the original coordinate a proper homomorphism.
Normalize Haar measure on the band `0 ≤ u ≤ 1`; Haar uniqueness on the real
line then identifies its pushforward with Lebesgue measure.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanHaar

open MeasureTheory TopologicalSpace Set Filter
open Cubic.QuadraticCorrespondence
open Cubic.ToricHeights.ArchimedeanQuotientLogarithm
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  ArchimedeanHaarData

local instance : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.isInducing.secondCountableTopology

local instance : SecondCountableTopology Points :=
  CyclotomicArchimedean.pointEquiv.toHomeomorph.secondCountableTopology

/-- A bounded logarithmic band is a compact annulus, including its angular direction. -/
theorem isCompact_complex_band (a b : ℝ) :
    IsCompact {z : ℂˣ | Real.log ‖(z : ℂ)‖ ∈ Icc a b} := by
  let S : Set ℂ := {z | Real.exp a ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp b}
  have hS : IsCompact S := by
    apply (isCompact_closedBall (0 : ℂ) (Real.exp b)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
  have hSrange : S ⊆ Set.range (fun z : ℂˣ => (z : ℂ)) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp ((Real.exp_pos a).trans_le hz.1)
    exact ⟨Units.mk0 z hz0, rfl⟩
  have hcompact := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS hSrange
  convert hcompact using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_preimage, S]
  rw [Real.le_log_iff_exp_le (norm_pos_iff.mpr z.ne_zero),
    Real.log_le_iff_le_exp (norm_pos_iff.mpr z.ne_zero)]

/-- Compactness is on the original evaluation topology, through its proved parametrization. -/
theorem isCompact_coordinate_band (a b : ℝ) : IsCompact (coordinate ⁻¹' Icc a b) :=
  CyclotomicArchimedean.pointEquiv.toHomeomorph.isCompact_preimage.mpr
    (isCompact_complex_band a b)

theorem coordinate_tendsto_cocompact :
    Tendsto coordinate (cocompact Points) (cocompact ℝ) := by
  apply Filter.hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hpre : IsCompact (coordinate ⁻¹' K) :=
    (isCompact_coordinate_band a b).of_isClosed_subset
      (hK.isClosed.preimage continuous_coordinate)
      (fun x hx => ⟨ha hx, hb hx⟩)
  exact hpre.compl_mem_cocompact

/-- A compact neighborhood whose logarithmic image spans one lattice interval. -/
def normalizationBand : PositiveCompacts Points where
  carrier := coordinate ⁻¹' Icc 0 1
  isCompact' := isCompact_coordinate_band 0 1
  interior_nonempty' := by
    have hO := (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)).preimage continuous_coordinate
    refine ⟨radialSection (1 / 2), ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hO.mem_nhds (by simp; norm_num))
    exact Set.preimage_mono Ioo_subset_Icc_self

local instance : LocallyCompactSpace Points := normalizationBand.locallyCompactSpace_of_group

local instance : SigmaCompactSpace Points := sigmaCompactSpace_of_locallyCompact_secondCountable

/-- Haar measure constructed on the original point group, independently of the Fourier formula. -/
def measure : Measure Points := Measure.haarMeasure normalizationBand

instance : measure.IsHaarMeasure := by unfold measure; infer_instance

theorem measure_band : measure (coordinate ⁻¹' Icc 0 1) = 1 := Measure.haarMeasure_self

/-- The additive logarithmic coordinate, written multiplicatively for Haar's map theorem. -/
def coordinateHom : Points →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (coordinate x)
  map_one' := coordinate_one
  map_mul' := coordinate_mul

local instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)
local instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

local instance : (show Measure (Multiplicative ℝ) from (volume : Measure ℝ)).IsHaarMeasure where
  map_mul_left_eq_self x := map_add_left_eq_self (volume : Measure ℝ) x.toAdd

/-- The scalar in the logarithmic pushforward is exactly one, by the unit-band normalization. -/
theorem map_measure : measure.map coordinate = volume := by
  let ν : Measure (Multiplicative ℝ) := measure.map coordinateHom
  letI : ν.IsHaarMeasure := Measure.isHaarMeasure_map measure coordinateHom
    continuous_coordinate coordinate_surjective coordinate_tendsto_cocompact
  let K : PositiveCompacts (Multiplicative ℝ) := PositiveCompacts.Icc01
  have hν : ν K = 1 := by
    change (measure.map coordinate) (Icc (0 : ℝ) 1) = 1
    rw [Measure.map_apply continuous_coordinate.measurable isCompact_Icc.measurableSet]
    exact measure_band
  have hvol : (show Measure (Multiplicative ℝ) from (volume : Measure ℝ)) K = 1 := by
    change volume (Icc (0 : ℝ) 1) = 1
    simp
  exact ((Measure.haarMeasure_eq_iff K ν).mpr hν).symm.trans
    ((Measure.haarMeasure_eq_iff K _).mpr hvol)

/-- The constructed measure realizes the paper's convention, including Haar invariance. -/
theorem normalized : ArchimedeanHaarData.NormalizedHaar measure :=
  ⟨inferInstance, map_measure⟩

/-- Every Haar measure with the paper's pushforward convention equals the constructed one. -/
theorem eq_measure (μ : Measure Points) (hμ : ArchimedeanHaarData.NormalizedHaar μ) :
    μ = measure := by
  letI : μ.IsHaarMeasure := hμ.1
  letI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  symm
  apply (Measure.haarMeasure_eq_iff normalizationBand μ).mpr
  have h := congrArg (fun ν : Measure ℝ => ν (Icc 0 1)) hμ.2
  change (μ.map coordinate) (Icc (0 : ℝ) 1) = volume (Icc (0 : ℝ) 1) at h
  rw [Measure.map_apply continuous_coordinate.measurable measurableSet_Icc] at h
  simpa only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] using h

theorem unique (μ ν : Measure Points)
    (hμ : ArchimedeanHaarData.NormalizedHaar μ) (hν : ArchimedeanHaarData.NormalizedHaar ν) :
    μ = ν := (eq_measure μ hμ).trans (eq_measure ν hν).symm

/-- The original logarithmic coordinate is measure preserving for the paper's measures. -/
theorem coordinate_measurePreserving : MeasurePreserving coordinate measure volume :=
  ⟨continuous_coordinate.measurable, map_measure⟩

theorem coordinate_unit_interval : measure (coordinate ⁻¹' Ioc 0 1) = 1 := by
  rw [← Measure.map_apply continuous_coordinate.measurable measurableSet_Ioc, map_measure]
  simp

end Cubic.PoissonSummation.ArchimedeanHaar
