import Cubic.ToricHeights.QuotientLocalHaar
import Cubic.ToricHeights.QuotientInvariantIntegrality
import Cubic.PoissonSummation.RamifiedLocalMeasure

/-!
# The original invariant cutoff and its exceptional Haar mass

The paper's cutoff is defined by the original functions `e₂`, `e₃` and `δ`.
It is closed in the regular-function topology. At three, the proved
measure-preserving parametrization identifies this cutoff with `1+3O`, giving
mass `1/6` for Haar measure normalized on the original maximal compact.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuotientLocalMeasure

open MeasureTheory
open Cubic.QuadraticCorrespondence
open CyclotomicTorusGalois
open Cubic.ToricHeights QuotientInvariantIntegrality
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalHaar RamifiedLocalModel

variable (p : ℕ) [Fact p.Prime]

/-- All three original regular-function integrality conditions define closed sets. -/
theorem isClosed_invariantLocus : IsClosed (invariantLocus p) :=
  (isClosed_le (RegularFunctionTopology.continuous_eval _).norm continuous_const).inter
    ((isClosed_le (RegularFunctionTopology.continuous_eval _).neg.norm continuous_const).inter
      (isClosed_le (RegularFunctionTopology.continuous_eval _).norm continuous_const))

theorem measurableSet_invariantLocus : MeasurableSet (invariantLocus p) :=
  (isClosed_invariantLocus p).measurableSet

/-- The original three-invariant cutoff is the exact preimage of the congruence locus. -/
theorem ramified_preimage_integralLocus :
    QuotientLocalModels.ramifiedEquiv ⁻¹' RamifiedLocalModel.integralLocus = invariantLocus 3 := by
  ext P
  change QuotientLocalModels.ramifiedEquiv P ∈ RamifiedLocalModel.integralLocus ↔ _
  rw [QuotientLocalModels.ramifiedEquiv_apply,
    ← RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus]
  exact (ramified_mem_iff P).symm

/-- The paper's exceptional factor on the original quotient, with its own normalized Haar measure. -/
theorem ramified_measure_invariantLocus :
    QuotientLocalHaar.ramifiedMeasure.real (invariantLocus 3) = 1 / 6 := by
  have h := QuotientLocalHaar.ramified_measurePreserving.measure_preimage
    RamifiedLocalModel.measurableSet_integralLocus.nullMeasurableSet
  rw [ramified_preimage_integralLocus] at h
  exact (congrArg ENNReal.toReal h).trans RamifiedLocalMeasure.measure_integralLocus

private theorem ramified_indicator_comp :
    (invariantLocus 3).indicator (fun _ => (1 : ℂ)) =
      (RamifiedLocalModel.integralLocus.indicator (fun _ => (1 : ℂ))) ∘
        QuotientLocalModels.ramifiedEquiv := by
  rw [← ramified_preimage_integralLocus]
  funext P
  dsimp only [Function.comp_apply]
  by_cases h : QuotientLocalModels.ramifiedEquiv P ∈ RamifiedLocalModel.integralLocus
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show
      P ∈ QuotientLocalModels.ramifiedEquiv ⁻¹' RamifiedLocalModel.integralLocus from h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show
      P ∉ QuotientLocalModels.ramifiedEquiv ⁻¹' RamifiedLocalModel.integralLocus from h)]

/-- Both integrability and the indicator integral hold on the original point space. -/
theorem ramified_integral_indicator :
    Integrable ((invariantLocus 3).indicator (fun _ => (1 : ℂ)))
      QuotientLocalHaar.ramifiedMeasure ∧
    (∫ P, (invariantLocus 3).indicator (fun _ => (1 : ℂ)) P
      ∂QuotientLocalHaar.ramifiedMeasure) = 1 / 6 := by
  rw [ramified_indicator_comp]
  refine ⟨(QuotientLocalHaar.ramified_measurePreserving.integrable_comp_emb
    QuotientLocalModels.ramifiedEquiv.toHomeomorph.measurableEmbedding).mpr
      RamifiedLocalMeasure.integral_indicator.1, ?_⟩
  exact (QuotientLocalHaar.ramified_measurePreserving.integral_comp
    QuotientLocalModels.ramifiedEquiv.toHomeomorph.measurableEmbedding _).trans
      RamifiedLocalMeasure.integral_indicator.2

end Cubic.PoissonSummation.QuotientLocalMeasure
