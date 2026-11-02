import Cubic.PoissonSummation.AdelicLevelArithmetic
import Cubic.PoissonSummation.AdelicHaar
import Cubic.PoissonSummation.HaarNormalization

/-!
# Haar mass of the finite congruence level

The actual finite Haar measure gives the full maximal compact mass one.
The arithmetic index six therefore gives the finite level mass `1/6`, the
finite factor used by the paper in its quotient-measure calculation.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevel

open MeasureTheory Set
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicCompactQuotient AdelicHeightZetaData QuotientFiniteFourierProduct
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  RestrictedProductHaar ArchimedeanHaarData AdelicHeightZetaData

theorem isOpen_localLevelModel : IsOpen (localLevelModel : Set RamifiedLocalModel.Points) := by
  have he : (localLevelModel : Set RamifiedLocalModel.Points) =
      (fun x : RamifiedLocalModel.Points => (x : CyclotomicRamifiedField.Extension)) ⁻¹'
        Metric.closedBall 1 (1 / 3) := by
    ext x
    rw [localLevelModel_carrier, RamifiedLocalModel.mem_integralLocus_iff_norm]
    simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  rw [he]
  exact (IsUltrametricDist.isOpen_closedBall _ (by norm_num : (1 / 3 : ℝ) ≠ 0)).preimage
    Units.continuous_val

theorem isOpen_ramifiedLevel : IsOpen (ramifiedLevel : Set (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[3])) :=
  isOpen_localLevelModel.preimage QuotientLocalModels.ramifiedEquiv.continuous

theorem isOpen_finiteCompact : IsOpen (finiteCompact : Set FiniteAdelicData.Points) :=
  RestrictedProductHaar.isOpen_compactSubgroup (fun p => (family p).Carrier)
    (fun p => (family p).maxCompact) (fun p => (family p).open_compact)

theorem continuous_atThree : Continuous atThree :=
  RestrictedProduct.continuous_eval FiniteEulerProduct.primeThree

theorem isOpen_finiteLevel : IsOpen (finiteLevel : Set FiniteAdelicData.Points) :=
  isOpen_finiteCompact.inter (isOpen_ramifiedLevel.preimage continuous_atThree)

theorem finiteLevelInCompact_image :
    Subtype.val '' (finiteLevelInCompact : Set finiteCompact) =
      (finiteLevel : Set FiniteAdelicData.Points) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx, rfl⟩

theorem finiteMeasure_compact : finiteMeasure (finiteCompact : Set FiniteAdelicData.Points) = 1 :=
  RestrictedProductHaar.measure_compactSubgroup _ _ _

theorem finiteMeasure_level_real : finiteMeasure.real (finiteLevel : Set FiniteAdelicData.Points) = 1 / 6 := by
  letI : finiteLevelInCompact.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [finiteLevelInCompact_index]; decide)
  have h := subgroup_index_mul_measure finiteMeasure finiteCompact
    isOpen_finiteCompact.measurableSet finiteLevelInCompact
    (isOpen_finiteLevel.preimage continuous_subtype_val).measurableSet
  rw [finiteLevelInCompact_index, finiteLevelInCompact_image] at h
  have hn : finiteMeasure.real (finiteCompact : Set FiniteAdelicData.Points) = 1 := by
    simp only [Measure.real, finiteMeasure_compact, ENNReal.toReal_one]
  rw [hn] at h
  norm_num at h
  linarith

theorem finiteMeasure_level_ne_top : finiteMeasure (finiteLevel : Set FiniteAdelicData.Points) ≠ ⊤ := by
  apply ne_of_lt
  exact (measure_mono finiteLevel_le_compact).trans_lt (by rw [finiteMeasure_compact]; simp)

theorem finiteMeasure_level : finiteMeasure (finiteLevel : Set FiniteAdelicData.Points) = 1 / 6 := by
  rw [← ENNReal.ofReal_toReal finiteMeasure_level_ne_top]
  change ENNReal.ofReal (finiteMeasure.real (finiteLevel : Set FiniteAdelicData.Points)) = _
  rw [finiteMeasure_level_real]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6)]
  norm_num

end Cubic.PoissonSummation.AdelicLevel
