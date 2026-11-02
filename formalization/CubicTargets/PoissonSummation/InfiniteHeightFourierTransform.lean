import CubicTargets.PoissonSummation.HeightFourierTransform

/-!
# Concrete statement of `eqn:infiniteHeightFourierTransform`

The objects are those of `prop:heightFourierTransform`; see
`CubicTargets.PoissonSummation.HeightFourierTransform` for the correspondence.
The standing hypotheses are those of the proposition: `Re s_e > 0` for every `e`, and `χ` is an
unramified unitary character of `T(ℝ)` with `χ = e(⟨ℓ_w(·), m⟩)` for `m ∈ 𝔱^∨`.
The equation is

  `Ĥ_∞(χ,-s,D₀) = (-1/2πi) · ((s₀+s₁+s₂)/2πi) · 1/((m(v₀)+s₀/2πi)(m(v₀)-(s₁+s₂)/2πi))`,

with `s₁ = s₂ = σ` and `v₀ = (-1,-1)`.
-/

namespace CubicTargets.PoissonSummation.InfiniteHeightFourierTransform

open Cubic.PoissonSummation.IntegralityStabilizer
open CubicTargets.PoissonSummation.HeightFourierTransform
open CubicTargets.PoissonSummation.ChimDefn (invariantDual)
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology

def Claim : Prop :=
  ∀ (χ : PontryaginDual Cubic.ToricHeights.ArchimedeanQuotientLogarithm.Points)
    (m : (ℝ × ℝ) →ₗ[ℝ] ℝ), (∀ k ∈ archimedeanMaxCompact, χ k = 1) → m ∈ invariantDual →
      IsExponential m χ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        infiniteFourier s₀ σ χ = infiniteFormula s₀ σ m

end CubicTargets.PoissonSummation.InfiniteHeightFourierTransform
