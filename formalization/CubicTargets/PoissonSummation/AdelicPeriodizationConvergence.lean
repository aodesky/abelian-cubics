import Cubic.PoissonSummation.AdelicHeightZetaData
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Spatial and periodization convergence used by the adelic Poisson argument

These conclusions precede the full-dual Fourier calculation. Keeping them in
their own supporting statement lets Fourier unfolding use their continuity
without depending on the completed `lemma:heightZetaConvergence`.
-/

namespace CubicTargets.PoissonSummation.AdelicPeriodizationConvergence

open MeasureTheory Cubic.PoissonSummation.AdelicHeightZetaData
open scoped Cubic.PoissonSummation.ArchimedeanHaarData
  Cubic.PoissonSummation.RestrictedProductHaar

structure Claim : Prop where
  spatial_integrable : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Integrable (cutoffHeight s₀ σ) measure
  periodization_absolute : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re → ∀ u : ℝ,
    Summable (fun γ : RationalPoints => ‖periodizationTerm s₀ σ γ u‖)
  periodization_locally_uniform : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    HasSumLocallyUniformly (periodizationTerm s₀ σ) (periodization s₀ σ)
  periodization_continuous : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Continuous (periodization s₀ σ)
  zeta_absolute : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Summable (fun γ : IntegralRationalPoints => ‖zetaTerm s₀ σ γ‖)

end CubicTargets.PoissonSummation.AdelicPeriodizationConvergence
