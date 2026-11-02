import Cubic.PoissonSummation.AdelicFourierSpectrumTopology
import Cubic.PoissonSummation.AdelicQuotientHaar
import Cubic.PoissonSummation.CompactAnnihilator

/-!
# Restriction of Haar measure to the surviving automorphic spectrum

The level is compact, so its annihilator is an open subgroup of the actual
automorphic dual. These facts justify restricting a Haar measure to the
surviving spectrum; the identification of its scalar with six must still use
the Fourier normalization of the full dual measure.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierSpectrum

open MeasureTheory Set
open AdelicRationalCharacter AdelicLevelQuotient AdelicLevel
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicQuotientMeasure ENNReal NNReal

theorem isCompact_level : IsCompact (level : Set AdelicData.Points) := by
  have ha : IsClosed (ArchimedeanHaar.coordinateHom.ker :
      Set Cubic.ToricHeights.ArchimedeanQuotientLogarithm.Points) := by
    change IsClosed (Cubic.ToricHeights.ArchimedeanQuotientLogarithm.coordinate ⁻¹' {0})
    exact isClosed_singleton.preimage
      Cubic.ToricHeights.ArchimedeanQuotientLogarithm.continuous_coordinate
  have hf : IsClosed (finiteLevel : Set FiniteAdelicData.Points) :=
    finiteLevel.isClosed_of_isOpen isOpen_finiteLevel
  exact AdelicCompactQuotient.isCompact_maximalCompact.of_isClosed_subset
    (ha.prod hf) level_le_maximalCompact

theorem isCompact_quotientLevel : IsCompact (quotientLevel : Set AutomorphicQuotient) :=
  isCompact_level.image QuotientGroup.continuous_mk

theorem isOpen_levelAnnihilator :
    IsOpen (levelAnnihilator : Set (PontryaginDual AutomorphicQuotient)) :=
  CompactAnnihilator.isOpen_setOf_trivial_on_compact quotientLevel isCompact_quotientLevel

/-- The original level annihilator, now with its proved openness. -/
def openLevelAnnihilator : OpenSubgroup (PontryaginDual AutomorphicQuotient) where
  __ := levelAnnihilator
  isOpen' := isOpen_levelAnnihilator

scoped instance : MeasurableSpace (PontryaginDual AutomorphicQuotient) :=
  borel (PontryaginDual AutomorphicQuotient)

scoped instance : BorelSpace (PontryaginDual AutomorphicQuotient) := ⟨rfl⟩

scoped instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)
scoped instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

open scoped AdelicFourierSpectrum

local instance : (show Measure (Multiplicative ℝ) from (volume : Measure ℝ)).IsHaarMeasure where
  map_mul_left_eq_self x := map_add_left_eq_self (volume : Measure ℝ) x.toAdd

theorem isOpenEmbedding_automorphicCharacter : Topology.IsOpenEmbedding automorphicCharacter :=
  isOpen_levelAnnihilator.isOpenEmbedding_subtypeVal.comp
    parameterEquiv.toHomeomorph.isOpenEmbedding

theorem range_automorphicCharacter :
    range automorphicCharacter = (levelAnnihilator : Set (PontryaginDual AutomorphicQuotient)) := by
  ext χ
  constructor
  · rintro ⟨t, rfl⟩
    exact automorphicCharacter_mem_levelAnnihilator t
  · intro hχ
    obtain ⟨t, ht⟩ := exists_parameter_of_level_trivial χ hχ
    exact ⟨t, ht.symm⟩

/-- Pull back the restriction of an actual full-spectrum measure; no scalar is
specified in this definition. -/
def spectralMeasure (ν : Measure (PontryaginDual AutomorphicQuotient)) : Measure ℝ :=
  ν.comap automorphicCharacter

theorem spectralMeasure_isHaar (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] :
    (show Measure (Multiplicative ℝ) from spectralMeasure ν).IsHaarMeasure := by
  let f : Multiplicative ℝ →* PontryaginDual AutomorphicQuotient :=
    levelAnnihilator.subtype.comp parameterHom.toMonoidHom
  exact Measure.IsHaarMeasure.comap ν (f := f) (mH := inferInstance)
    isOpenEmbedding_automorphicCharacter

/-- The undetermined positive scalar of the restriction, before Fourier normalization. -/
def spectralScalar (ν : Measure (PontryaginDual AutomorphicQuotient)) [ν.IsHaarMeasure] : ℝ≥0 := by
  letI := spectralMeasure_isHaar ν
  exact Measure.haarScalarFactor (show Measure (Multiplicative ℝ) from spectralMeasure ν)
    (show Measure (Multiplicative ℝ) from (volume : Measure ℝ))

theorem spectralScalar_pos (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] : 0 < spectralScalar ν := by
  letI := spectralMeasure_isHaar ν
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure
    (show Measure (Multiplicative ℝ) from spectralMeasure ν)
    (show Measure (Multiplicative ℝ) from (volume : Measure ℝ))

theorem spectralMeasure_eq_smul (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] : spectralMeasure ν = spectralScalar ν • volume := by
  letI := spectralMeasure_isHaar ν
  exact Measure.isMulLeftInvariant_eq_smul
    (show Measure (Multiplicative ℝ) from spectralMeasure ν)
    (show Measure (Multiplicative ℝ) from (volume : Measure ℝ))

theorem map_spectralMeasure (ν : Measure (PontryaginDual AutomorphicQuotient)) :
    (spectralMeasure ν).map automorphicCharacter = ν.restrict levelAnnihilator := by
  rw [spectralMeasure, isOpenEmbedding_automorphicCharacter.measurableEmbedding.map_comap,
    range_automorphicCharacter]

/-- Absolute integrability on the full spectrum is exactly the real-coordinate
condition when the function vanishes off the prescribed level annihilator. -/
theorem integrable_iff_coordinate (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] (f : PontryaginDual AutomorphicQuotient → ℂ)
    (hsupp : Function.support f ⊆ levelAnnihilator) :
    Integrable f ν ↔ Integrable (fun t : ℝ => f (automorphicCharacter t)) := by
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, IntegrableOn,
    ← map_spectralMeasure, isOpenEmbedding_automorphicCharacter.measurableEmbedding.integrable_map_iff,
    spectralMeasure_eq_smul]
  exact integrable_smul_measure (by simpa using (spectralScalar_pos ν).ne') (by simp)

/-- Transfer an integral supported on the surviving characters to the real line,
retaining the scalar of the actual full-spectrum Haar measure. -/
theorem integral_eq_scalar_mul (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] (f : PontryaginDual AutomorphicQuotient → ℂ)
    (hsupp : Function.support f ⊆ levelAnnihilator) :
    (∫ χ, f χ ∂ν) = (spectralScalar ν : ℂ) * ∫ t : ℝ, f (automorphicCharacter t) := by
  have hind : (levelAnnihilator : Set (PontryaginDual AutomorphicQuotient)).indicator f = f :=
    Set.indicator_eq_self.mpr hsupp
  rw [← hind, integral_indicator isOpen_levelAnnihilator.measurableSet, hind,
    ← map_spectralMeasure, isOpenEmbedding_automorphicCharacter.measurableEmbedding.integral_map,
    spectralMeasure_eq_smul]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Cubic.PoissonSummation.AdelicFourierSpectrum
