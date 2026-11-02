import Cubic.ToricHeights.RamifiedLocalModel
import Cubic.PoissonSummation.HaarNormalization
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The mass of the exceptional congruence subgroup

The index-six theorem now applies to the actual local compact unit group.
Consequently `1+3𝓞` has Haar mass `1/6`. This evaluates its indicator integral;
`RamifiedLocalFourier.lean` subsequently identifies the constructed local
height-character integrand with this indicator. The original torus comparison
remains separate.
-/

noncomputable section

namespace Cubic.PoissonSummation.RamifiedLocalMeasure

open MeasureTheory
open Cubic.ToricHeights.RamifiedLocalModel
open Cubic.QuadraticCorrespondence.CyclotomicRamifiedField (isOpen_compactUnits)

theorem measure_integralLocus : measure.real integralLocus = 1 / 6 := by
  letI : congruenceSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [congruenceSubgroup_index]; decide)
  have h := subgroup_index_mul_measure measure compactUnits
    isOpen_compactUnits.measurableSet congruenceSubgroup measurableSet_congruenceSubgroup
  rw [congruenceSubgroup_index] at h
  have hnorm : measure.real (compactUnits : Set Points) = 1 := by
    simp [Measure.real, measure_compactUnits]
  rw [hnorm] at h
  norm_num at h
  change measure.real (Subtype.val '' (congruenceSubgroup : Set compactUnits)) = _
  linarith

/-- The actual congruence indicator is integrable and its integral is `1/6`. -/
theorem integral_indicator :
    Integrable (integralLocus.indicator (fun _ => (1 : ℂ))) measure ∧
      (∫ x, integralLocus.indicator (fun _ => (1 : ℂ)) x ∂measure) = 1 / 6 := by
  have hfinite : measure integralLocus ≠ ⊤ := ne_of_lt
    ((measure_mono integralLocus_subset).trans_lt (by rw [measure_compactUnits]; simp))
  refine ⟨(integrable_indicator_iff measurableSet_integralLocus).mpr
    (integrableOn_const hfinite), ?_⟩
  rw [integral_indicator_const (μ := measure) _ measurableSet_integralLocus,
    measure_integralLocus]
  norm_num

end Cubic.PoissonSummation.RamifiedLocalMeasure
