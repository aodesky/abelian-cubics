import Cubic.SantensComparison.RamifiedGaugeVolume
import Cubic.SantensComparison.NormalizedLocalVolumes
import Cubic.PoissonSummation.RamifiedLocalMeasure

/-! The logarithmic differential fixes a unique Haar measure at three.
Its mass on 1+3O is the actual coordinate integral. Haar uniqueness and the
proved subgroup index determine its normalization on the entire local torus. -/

noncomputable section

namespace Cubic.SantensComparison.RamifiedHaarNormalization

open MeasureTheory Cubic.ToricHeights
open Cubic.QuadraticCorrespondence
open scoped RamifiedLocalModel

local instance : SecondCountableTopology RamifiedLocalModel.Points := by
  letI : SecondCountableTopology CyclotomicRamifiedField.Extensionᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : CyclotomicRamifiedField.Extension ≃ₜ
      CyclotomicRamifiedField.Extensionᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

def scale : ℝ :=
  RamifiedLocalModel.congruenceSubgroup.index * RamifiedGaugeVolume.gaugeVolume

def gaugeMeasure : Measure RamifiedLocalModel.Points :=
  ENNReal.ofReal scale • RamifiedLocalModel.measure

theorem scale_value : scale=2/(3*Real.sqrt 3) := by
  rw [scale, RamifiedLocalModel.congruenceSubgroup_index, RamifiedGaugeVolume.gauge_volume]
  ring

theorem scale_pos : 0 < scale := by
  rw [scale_value]
  positivity

theorem original_subgroup_mass :
    RamifiedLocalModel.measure RamifiedLocalModel.integralLocus=ENNReal.ofReal (1/6:ℝ) := by
  have hf : RamifiedLocalModel.measure RamifiedLocalModel.integralLocus ≠ ⊤ := ne_of_lt
    ((measure_mono RamifiedLocalModel.integralLocus_subset).trans_lt (by
      rw [RamifiedLocalModel.measure_compactUnits]; simp))
  apply (ENNReal.toReal_eq_toReal_iff' hf ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  exact Cubic.PoissonSummation.RamifiedLocalMeasure.measure_integralLocus

theorem normalization : gaugeMeasure RamifiedLocalModel.integralLocus=
    ENNReal.ofReal RamifiedGaugeVolume.gaugeVolume := by
  rw [gaugeMeasure, Measure.smul_apply, smul_eq_mul, original_subgroup_mass,
    ← ENNReal.ofReal_mul scale_pos.le]
  congr 1
  rw [scale, RamifiedLocalModel.congruenceSubgroup_index]
  ring

theorem gauge_unique (μ : Measure RamifiedLocalModel.Points)
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hμ : μ RamifiedLocalModel.integralLocus=
      ENNReal.ofReal RamifiedGaugeVolume.gaugeVolume) : μ=gaugeMeasure := by
  have hu := Measure.haarMeasure_unique μ RamifiedLocalModel.compactNeighborhood
  change μ=μ RamifiedLocalModel.compactUnits • RamifiedLocalModel.measure at hu
  have hc : μ RamifiedLocalModel.compactUnits * ENNReal.ofReal (1/6:ℝ)=
      ENNReal.ofReal RamifiedGaugeVolume.gaugeVolume := by
    rw [← original_subgroup_mass, ← smul_eq_mul, ← Measure.smul_apply, ← hu]
    exact hμ
  have hd : ENNReal.ofReal scale * ENNReal.ofReal (1/6:ℝ)=
      ENNReal.ofReal RamifiedGaugeVolume.gaugeVolume := by
    simpa only [gaugeMeasure, Measure.smul_apply, smul_eq_mul, original_subgroup_mass] using
      normalization
  have he := (ENNReal.mul_left_inj (by norm_num : ENNReal.ofReal (1/6:ℝ) ≠ 0)
    ENNReal.ofReal_ne_top).mp (hc.trans hd.symm)
  rw [hu, he]
  rfl

theorem paper_norm_integral :
    (∫ x, LocalVolumeData.ramifiedWeight x ∂gaugeMeasure)=RamifiedGaugeVolume.gaugeVolume := by
  rw [gaugeMeasure, integral_smul_measure, ENNReal.toReal_ofReal scale_pos.le]
  change scale*LocalVolumeData.ramifiedMoment=RamifiedGaugeVolume.gaugeVolume
  rw [NormalizedLocalVolumes.ramified_moment.2, scale,
    RamifiedLocalModel.congruenceSubgroup_index]
  ring

end Cubic.SantensComparison.RamifiedHaarNormalization
