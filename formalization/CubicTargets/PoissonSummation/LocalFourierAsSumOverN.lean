import CubicTargets.PoissonSummation.HeightFourierTransform

/-!
# Concrete statement of `eqn:localfourierassumovern`

This is a step in the proof of `prop:heightFourierTransform`. The objects are those of the
proposition; see `CubicTargets.PoissonSummation.HeightFourierTransform`.
The context is the same: `v ≠ 3` is finite, `w | v`, and `N_w = X_*(T_E)^{Γ(w/v)}`.
`χ` is an unramified unitary character of `T(ℚ_v)`, regarded as the character `ψ` of `N_w`
(`Descends`), and `Re s_e > 0` for every `e`. The equation is

  `∫_{T(ℚ_v)} H_v(x,s)^{-1} 1_v^{D₀}(x) χ(x)^{-1} d^×x_v
     = ∑_{n ∈ N_w} q_v^{φ(n)/e_v} 1_v^{D₀}(n) χ(n)^{-1}
     = ∑_{n ∈ N_w ∩ (ℝ≥0 v₁ + ℝ≥0 v₂)} χ(n)^{-1} q_v^{φ(n)}`.

* `H_v(x,s)^{-1} = H_v(x,-s)` is the project's local inverse height, as in the proposition.
* `v ≠ 3` is unramified in `E`, so `e_v = 1` and the exponent is `φ(n)`.
* `1_v^{D₀}(n)` is the descent of `1_v^{D₀}` to `N_w`, which the paper uses implicitly. It is
  stated as a function `ind'` on `N_w` with `1_v^{D₀}(x) = ind'(ℓ_w x)`. Since `ℓ_w` is onto `N_w`
  (`prop:basicfacts`), `ind'` is unique, so the existential quantifier adds nothing.
* The integral converges absolutely, and both sums converge (`HasSum`).
-/

namespace CubicTargets.PoissonSummation.LocalFourierAsSumOverN

open MeasureTheory
open Cubic.QuadraticCorrespondence Cubic.ToricHeights Cubic.PoissonSummation
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology QuotientLocalHaar

/-- The conclusion of `eqn:localfourierassumovern` at one place, for `ψ` and `s`. -/
def SumOverN {G : Type} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (D : DecompositionGroup) (ℓ : G → ℤ × ℤ) (q : ℕ) (height : G → ℂ) (ind : G → ℝ)
    (χ : PontryaginDual G) (ψ : Multiplicative (invariantLattice D) →* Circle) (s₀ σ : ℂ) : Prop :=
  Integrable (fun x => height x * (ind x : ℂ) * ((χ x : Circle) : ℂ)⁻¹) μ ∧
    ∃ ind' : invariantLattice D → ℝ,
      (∀ (x : G) (n : invariantLattice D), (n : ℤ × ℤ) = ℓ x → ind x = ind' n) ∧
      HasSum (fun n : invariantLattice D =>
          (q : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding n) * (ind' n : ℂ) *
            ((ψ (Multiplicative.ofAdd n) : Circle) : ℂ)⁻¹)
        (∫ x, height x * (ind x : ℂ) * ((χ x : Circle) : ℂ)⁻¹ ∂μ) ∧
      HasSum (coneTerm D q s₀ σ ψ) (∫ x, height x * (ind x : ℂ) * ((χ x : Circle) : ℂ)⁻¹ ∂μ)

structure Claim : Prop where
  split_first : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ QuotientLocalHaar.splitCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .trivial (splitCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        SumOverN (QuotientLocalHaar.splitMeasure p) .trivial (splitCochar p) (residueCard p)
          (QuotientFiniteHeight.splitInverseHeight p s₀ σ)
          (IntegralityStabilizer.localIndicatorAt p) χ ψ s₀ σ
  split_second : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ QuotientLocalHaar.splitCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .trivial (splitSecondCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        SumOverN (QuotientLocalHaar.splitMeasure p) .trivial (splitSecondCochar p) (residueCard p)
          (QuotientFiniteHeight.splitInverseHeight p s₀ σ)
          (IntegralityStabilizer.localIndicatorAt p) χ ψ s₀ σ
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (χ : PontryaginDual (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])),
    (∀ k ∈ QuotientLocalHaar.inertCompactUnits p, χ k = 1) →
      ∀ ψ, Descends .whole (inertCochar p) χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        SumOverN (QuotientLocalHaar.inertMeasure p) .whole (inertCochar p) (residueCard p)
          (QuotientFiniteHeight.inertInverseHeight p s₀ σ)
          (IntegralityStabilizer.localIndicatorAt p) χ ψ s₀ σ

end CubicTargets.PoissonSummation.LocalFourierAsSumOverN
