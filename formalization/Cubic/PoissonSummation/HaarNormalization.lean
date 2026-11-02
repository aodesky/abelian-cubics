import Mathlib.MeasureTheory.Group.Measure

/-!
# Normalization on finite-index subgroups of a local compact subgroup

Transfer mathlib's `Subgroup.index_mul_measure` along the inclusion into the
ambient local group. This is the measure calculation used at the exceptional
prime in `lemma:finiteFourierProduct`. `RamifiedLocalModel.lean` supplies the
arithmetic index for the actual local field; this helper keeps it as a parameter.
-/

namespace Cubic.PoissonSummation

open MeasureTheory

/-- The ambient measure of a subgroup of `K` is determined by its index in `K`.
The formula uses real-valued measure, as required by Bochner integration. -/
theorem subgroup_index_mul_measure {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (H : Subgroup K) [H.FiniteIndex] (hH : MeasurableSet (H : Set K)) :
    (H.index : ℝ) * μ.real (Subtype.val '' (H : Set K)) = μ.real (K : Set G) := by
  letI : MeasurableMul K := {
    measurable_const_mul c := (measurable_subtype_coe.const_mul (c : G)).subtype_mk
    measurable_mul_const c := (measurable_subtype_coe.mul_const (c : G)).subtype_mk }
  have hf : MeasurableEmbedding K.subtype := MeasurableEmbedding.subtype_coe hK
  letI : (μ.comap K.subtype).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hf
  have h := MeasureTheory.Subgroup.index_mul_measure H hH (μ.comap K.subtype)
  rw [hf.comap_apply, hf.comap_apply] at h
  have hfull : K.subtype '' Set.univ = (K : Set G) := by ext; simp
  rw [hfull] at h
  simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

end Cubic.PoissonSummation
