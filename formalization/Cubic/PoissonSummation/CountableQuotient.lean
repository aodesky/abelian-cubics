import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Integration through a normalized countable quotient

The finite-place valuation map has maximal compact kernel of Haar mass one.
Its pushforward measure is therefore counting measure. This gives both local
integrability and the lattice-sum formula from a summable function on the quotient.
The map, its kernel and the integrand identification must still be supplied by
the geometry; no integral evaluation is assumed here.
-/

noncomputable section

namespace Cubic.PoissonSummation

open MeasureTheory

/-- A homomorphism to a countable group is measurable when its kernel is.
Every nonempty fiber is a translate of the kernel. -/
theorem measurable_of_countable_ker
    {G Γ : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (v : G →* Γ) (hker : MeasurableSet (v.ker : Set G)) : Measurable v := by
  apply measurable_to_countable
  intro g
  have hfiber : v ⁻¹' {v g} = (fun x => g⁻¹ * x) ⁻¹' (v.ker : Set G) := by
    ext x
    change v x = v g ↔ v (g⁻¹ * x) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact eq_comm
  rw [hfiber]
  exact hker.preimage (measurable_const_mul g⁻¹)

/-- A surjective measurable homomorphism with kernel of mass one sends a left
invariant measure to counting measure on its countable target. -/
theorem measurePreserving_count_of_ker
    {G Γ : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group Γ] [Countable Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (v : G →* Γ)
    (hv : Measurable v) (hsurj : Function.Surjective v) (hker : μ (v.ker : Set G) = 1) :
    MeasurePreserving v μ Measure.count := by
  refine ⟨hv, Measure.ext_of_singleton fun n => ?_⟩
  rw [Measure.map_apply hv (measurableSet_singleton n)]
  obtain ⟨g, rfl⟩ := hsurj n
  have hfiber : v ⁻¹' {v g} = (fun x => g⁻¹ * x) ⁻¹' (v.ker : Set G) := by
    ext x
    change v x = v g ↔ v (g⁻¹ * x) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact eq_comm
  rw [hfiber, measure_preimage_mul, hker]
  simp

/-- Integrability and integration of an absolutely summable function pulled back
from a countable quotient. This uses mathlib's change-of-variables theorem. -/
theorem integrable_and_integral_eq_tsum_of_count
    {G Γ : Type*} [MeasurableSpace G] [Countable Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    {μ : Measure G} {v : G → Γ} (hv : MeasurePreserving v μ Measure.count)
    {f : Γ → ℂ} (hf : Summable f) :
    Integrable (f ∘ v) μ ∧ (∫ x, f (v x) ∂μ) = ∑' n, f n := by
  have hi : Integrable f Measure.count := integrable_count_iff.mpr hf.norm
  refine ⟨hv.integrable_comp_of_integrable hi, ?_⟩
  have hm : AEStronglyMeasurable f (Measure.map v μ) := by
    rw [hv.map_eq]
    exact hi.aestronglyMeasurable
  rw [← integral_map hv.measurable.aemeasurable hm, hv.map_eq, integral_countable' hi]
  simp [Measure.real]

/-- The quotient sum may be indexed only by the cone: extend its weights by zero
outside the embedded cone, without imposing integrability as a hypothesis. -/
theorem integrable_and_integral_eq_tsum_of_extend
    {G Γ I : Type*} [MeasurableSpace G] [Countable Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    {μ : Measure G} {v : G → Γ} (hv : MeasurePreserving v μ Measure.count)
    (e : I ↪ Γ) {w : I → ℂ} (hw : Summable w) :
    Integrable ((Function.extend e w 0) ∘ v) μ ∧
      (∫ x, Function.extend e w 0 (v x) ∂μ) = ∑' n, w n := by
  have h := integrable_and_integral_eq_tsum_of_count hv
    ((summable_extend_zero e.injective).mpr hw)
  simpa only [tsum_extend_zero e.injective] using h

end Cubic.PoissonSummation
