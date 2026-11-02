import Cubic.PoissonSummation.AdelicLevelQuotientData
import Cubic.PoissonSummation.LogarithmExactSequence

/-!
# The logarithm isomorphism on the double quotient

Follow `lemma:KprimeGroup`: `prop:Lmap` identifies the kernel with the compact
image, and the six-unit reduction replaces that compact image by the level
image. The actual radial section supplies the inverse. Finally, composition
of measure pushforwards gives the normalization already computed on the
counting-normalized rational quotient.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevelQuotient

open MeasureTheory
open AdelicRationalCharacter AdelicCompactQuotient AdelicLevel
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData ENNReal

/-- The paper's kernel argument: `Kmax = μmax K^{D₀}` after the exact sequence. -/
theorem quotientLevel_eq_ker : quotientLevel = quotientCoordinate.ker := by
  apply le_antisymm quotientLevel_le_ker
  intro x hx
  rw [← Cubic.PoissonSummation.«prop:Lmap».exact] at hx
  obtain ⟨k, rfl⟩ := hx
  induction k using QuotientGroup.induction_on with
  | H k =>
    obtain ⟨u, hu⟩ := exists_unit_correction k
    refine ⟨(RationalAdelicEmbedding.diagonal (RationalUnitReduction.rationalUnit u))⁻¹ *
      (k : AdelicData.Points), hu, ?_⟩
    change QuotientGroup.mk (_⁻¹ * (k : AdelicData.Points)) =
      (QuotientGroup.mk (k : AdelicData.Points) : AutomorphicQuotient)
    have hunit : (QuotientGroup.mk
        (RationalAdelicEmbedding.diagonal (RationalUnitReduction.rationalUnit u)) :
        AutomorphicQuotient) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hunit, inv_one, one_mul]

@[simp]
theorem logarithm_quotientProjection (x : AutomorphicQuotient) :
    logarithm (quotientProjection x) = quotientCoordinate x := rfl

@[simp]
theorem logarithm_projection (x : AdelicData.Points) :
    logarithm (projection x) = coordinate x := rfl

@[simp]
theorem logarithm_radial (u : ℝ) : logarithm (radial u) = Multiplicative.ofAdd u :=
  coordinate_radialSection u

theorem logarithm_injective : Function.Injective logarithm := by
  apply (injective_iff_map_eq_one logarithm).mpr
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    rw [quotientLevel_eq_ker]
    exact hx

theorem logarithm_surjective : Function.Surjective logarithm :=
  fun u => ⟨radial u.toAdd, logarithm_radial u.toAdd⟩

theorem continuous_logarithm : Continuous logarithm :=
  (QuotientGroup.isQuotientMap_mk quotientLevel).continuous_iff.mpr
    continuous_quotientCoordinate

theorem continuous_quotientProjection : Continuous quotientProjection :=
  QuotientGroup.continuous_mk

theorem continuous_projection : Continuous projection :=
  continuous_quotientProjection.comp QuotientGroup.continuous_mk

theorem continuous_radial : Continuous radial :=
  continuous_projection.comp AdelicData.continuous_radialSection

/-- The original logarithm, with the paper's radial section as continuous inverse. -/
def logarithmEquiv : DoubleQuotient ≃ₜ* Multiplicative ℝ where
  toFun := logarithm
  invFun u := radial u.toAdd
  left_inv x := logarithm_injective (logarithm_radial (logarithm x).toAdd)
  right_inv u := logarithm_radial u.toAdd
  map_mul' := logarithm.map_mul
  continuous_toFun := continuous_logarithm
  continuous_invFun := continuous_radial

@[simp]
theorem logarithmEquiv_apply (x : DoubleQuotient) : logarithmEquiv x = logarithm x := rfl

@[simp]
theorem logarithmEquiv_symm_apply (u : ℝ) :
    logarithmEquiv.symm (Multiplicative.ofAdd u) = radial u := rfl

/-- The measurable structure is the actual iterated quotient structure. -/
theorem measurable_realCoordinate : Measurable realCoordinate := by
  apply QuotientGroup.measurable_from_quotient.mpr
  exact AdelicQuotientMeasure.measurable_quotientRealCoordinate

/-- No new normalization choice: compose the existing quotient pushforward with the level map. -/
theorem map_measure_realCoordinate :
    measure.map realCoordinate = (1 / 6 : ℝ≥0∞) • volume := by
  have hq : Measurable quotientProjection := QuotientGroup.measurable_coe
  rw [measure, Measure.map_map measurable_realCoordinate hq]
  exact AdelicQuotientMeasure.map_quotientMeasure_coordinate

end Cubic.PoissonSummation.AdelicLevelQuotient
