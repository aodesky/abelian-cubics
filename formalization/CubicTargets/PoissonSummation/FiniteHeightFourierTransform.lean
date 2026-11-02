import CubicTargets.PoissonSummation.HeightFourierTransform

/-!
# Concrete statement of `eqn:finiteHeightFourierTransform`

The objects are those of `prop:heightFourierTransform`; see
`CubicTargets.PoissonSummation.HeightFourierTransform` for the correspondence.
The context is that of the proposition. `v ≠ 3` is a finite place and `w | v` is any place of `E`.
`χ` is an unramified unitary character of `T(ℚ_v)`, regarded through `ℓ_w` as the character `ψ` of
`X_*(T_E)^{Γ(w/v)}` (`Descends`). `Re s_e > 0` for every `e`. The equation

  `Ĥ_v(χ,-s,D₀) = ∑_{n ∈ X_*(T_E)^{Γ(w/v)}, n ∈ ℝ≥0 v₁ + ℝ≥0 v₂} χ(n)^{-1} q_v^{φ(n)}`

is stated as `HasSum`, so it includes convergence of the sum. The places `w | v ≠ 3` are:
the two places over a split prime (`p ≡ 1 mod 3`), and the unique place over an inert prime
(`p ≡ 2 mod 3`, including `p = 2`).
-/

namespace CubicTargets.PoissonSummation.FiniteHeightFourierTransform

open Cubic.QuadraticCorrespondence
open CubicTargets.PoissonSummation.HeightFourierTransform
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

structure Claim : Prop where
  split_first : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ Cubic.ToricHeights.QuotientLocalHaar.splitCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .trivial (splitCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        HasSum (coneTerm .trivial (residueCard p) s₀ σ ψ) (splitFourier p s₀ σ χ)
  split_second : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ Cubic.ToricHeights.QuotientLocalHaar.splitCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .trivial (splitSecondCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        HasSum (coneTerm .trivial (residueCard p) s₀ σ ψ) (splitFourier p s₀ σ χ)
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ Cubic.ToricHeights.QuotientLocalHaar.inertCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .whole (inertCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        HasSum (coneTerm .whole (residueCard p) s₀ σ ψ) (inertFourier p s₀ σ χ)

end CubicTargets.PoissonSummation.FiniteHeightFourierTransform
