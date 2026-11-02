import CubicTargets.PoissonSummation.FiniteFourierProduct

/-!
# Comparing actual local Fourier integrals

A measure-preserving topological group isomorphism, together with pointwise
height, cutoff and character comparisons, transfers both integrability and the
Bochner integral. No Fourier value or convergence conclusion is assumed.
-/

namespace Cubic.PoissonSummation.LocalFourierComparison

open MeasureTheory
open CubicTargets.PoissonSummation.FiniteFourierProduct

/-- The exact data needed to change variables in the paper's local Fourier integral. -/
structure Comparison (D F : LocalData) where
  equiv : D.Carrier ≃ₜ* F.Carrier
  measurePreserving : MeasurePreserving equiv D.measure F.measure
  inverseHeight_eq : ∀ s₀ σ x, D.inverseHeight s₀ σ x = F.inverseHeight s₀ σ (equiv x)
  integralLocus_eq : equiv ⁻¹' F.integralLocus = D.integralLocus
  character_eq : ∀ t x, D.character t x = F.character t (equiv x)

variable {D F : LocalData} (C : Comparison D F)

include C

theorem localIntegrand_eq (s₀ σ : ℂ) (t : ℝ) :
    localIntegrand D s₀ σ t = (localIntegrand F s₀ σ t) ∘ C.equiv := by
  funext x
  dsimp only [localIntegrand, Function.comp_apply]
  rw [C.character_eq]
  have hx : x ∈ D.integralLocus ↔ C.equiv x ∈ F.integralLocus := by
    rw [← C.integralLocus_eq]
    rfl
  by_cases h : x ∈ D.integralLocus
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hx.mp h), C.inverseHeight_eq]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hx.mpr h)]

theorem integrable_iff (s₀ σ : ℂ) (t : ℝ) :
    Integrable (localIntegrand D s₀ σ t) D.measure ↔
      Integrable (localIntegrand F s₀ σ t) F.measure := by
  rw [localIntegrand_eq C]
  exact C.measurePreserving.integrable_comp_emb C.equiv.toHomeomorph.measurableEmbedding

theorem localFourier_eq (s₀ σ : ℂ) (t : ℝ) :
    localFourier D s₀ σ t = localFourier F s₀ σ t := by
  change (∫ x, localIntegrand D s₀ σ t x ∂D.measure) =
    ∫ y, localIntegrand F s₀ σ t y ∂F.measure
  rw [localIntegrand_eq C]
  exact C.measurePreserving.integral_comp C.equiv.toHomeomorph.measurableEmbedding _

end Cubic.PoissonSummation.LocalFourierComparison
