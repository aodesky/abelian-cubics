import CubicTargets.PoissonSummation.PoissonIntegral

/-!
# `eqn:poissonEulerIntegral`

`Z(s) = 6 ∫_ℝ Ĥ_∞(χ_{m,∞}, −s, D₀) Ĥ_fin(χ_m, −s, D₀) dt`.

This is the displayed equation of `lemma:poissonIntegral`, with the same objects: the
original reciprocal-height series and the local Haar integrals
(`AdelicSpectralIntegrand.integrand`). It is stated in the lemma's parameter region.
Integrability of the right side is included, so the Bochner integral is genuine.
-/

namespace CubicTargets.PoissonSummation.PoissonEulerIntegral

open MeasureTheory Cubic.PoissonSummation

def Claim : Prop :=
  ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Integrable (AdelicSpectralIntegrand.integrand s₀ σ) ∧
      AdelicHeightZetaData.heightZeta s₀ σ = 6 * ∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t

end CubicTargets.PoissonSummation.PoissonEulerIntegral
