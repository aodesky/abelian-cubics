import Cubic.ToricHeights.RamifiedLocalHeight
import Cubic.ToricHeights.RamifiedLocalIntegrality
import Cubic.PoissonSummation.RamifiedLocalMeasure
import CubicTargets.PoissonSummation.FiniteFourierProduct

/-!
# The Fourier integral at three

Evaluate the actual local integral, using the support-function height,
spectral character and integrality of the paper's cubic coefficient expressions.
The equivalence of that cutoff with `1+3𝓞` is proved. Both height and character are one
on the compact unit group, and the proved congruence index gives the mass.
This completes the exceptional local model; its comparison with the paper's
original torus and geometric integrality condition remains necessary.
-/

noncomputable section

namespace Cubic.PoissonSummation.RamifiedLocalFourier

open MeasureTheory
open Cubic.ToricHeights
open Cubic.QuadraticCorrespondence
open CubicTargets.PoissonSummation.FiniteFourierProduct
open scoped RamifiedLocalModel

/-- Concrete local data on the units of the actual ramified extension. -/
def data : LocalData where
  Carrier := RamifiedLocalModel.Points
  maxCompact := RamifiedLocalModel.compactUnits
  compact := CyclotomicRamifiedField.isCompact_compactUnits
  open_compact := CyclotomicRamifiedField.isOpen_compactUnits
  maximal := CyclotomicRamifiedField.compact_subgroup_le
  measure := RamifiedLocalModel.measure
  normalized := RamifiedLocalModel.measure_compactUnits
  inverseHeight := RamifiedLocalModel.inverseHeight
  integralLocus := RamifiedLocalIntegrality.coefficientLocus
  measurable_integralLocus := by
    rw [RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus]
    exact RamifiedLocalModel.measurableSet_integralLocus
  character := RamifiedLocalModel.character
  character_zero := RamifiedLocalModel.character_zero

/-- The Fourier integrand reduces pointwise to the actual congruence indicator. -/
theorem integrand_eq_indicator (s₀ σ : ℂ) (t : ℝ) :
    localIntegrand data s₀ σ t = RamifiedLocalModel.integralLocus.indicator (fun _ => (1 : ℂ)) := by
  funext x
  change RamifiedLocalIntegrality.coefficientLocus.indicator (RamifiedLocalModel.inverseHeight s₀ σ) x *
      ((RamifiedLocalModel.character t x : Circle) : ℂ)⁻¹ = _
  rw [RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus]
  by_cases hx : x ∈ RamifiedLocalModel.integralLocus
  · have hK := RamifiedLocalModel.integralLocus_subset hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      RamifiedLocalModel.inverseHeight_on_compactUnits s₀ σ x hK,
      RamifiedLocalModel.character_on_compactUnits t x hK]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- The exceptional factor, with no integral evaluation or support hypothesis assumed.
Compact support makes this valid for all parameters. -/
theorem integral_eq_one_sixth (s₀ σ : ℂ) (t : ℝ) :
    Integrable (localIntegrand data s₀ σ t) data.measure ∧
      localFourier data s₀ σ t = 1 / 6 := by
  change Integrable (localIntegrand data s₀ σ t) RamifiedLocalModel.measure ∧
    (∫ x, localIntegrand data s₀ σ t x ∂RamifiedLocalModel.measure) = 1 / 6
  rw [integrand_eq_indicator]
  exact RamifiedLocalMeasure.integral_indicator

end Cubic.PoissonSummation.RamifiedLocalFourier
