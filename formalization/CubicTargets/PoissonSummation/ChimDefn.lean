import Cubic.PoissonSummation.AdelicLevelQuotientData

/-!
# Concrete statement of `eqn:chimdefn`

Every automorphic character trivial on `K^{D₀}` is `χₘ(x) = e(⟨m, ℓ(x)⟩)` for an
`m ∈ 𝔱^∨`, where `e(u) = exp(2π i u)`.

## Correspondence with the paper

* `T(ℚ)\T(𝔸)` is `AdelicRationalCharacter.AutomorphicQuotient`, the original
  adelic group `AdelicData.Points` modulo the proved rational diagonal; automorphic
  characters are its continuous unitary characters `PontryaginDual AutomorphicQuotient`.
* `K^{D₀}` is `AdelicLevel.level`; "trivial on `K^{D₀}`" is stated literally on the
  images of its elements.
* `𝔱_E = N_E ⊗ ℝ` is `ℝ × ℝ` in the ray coordinates used throughout the project
  (`v₁ = (1,0)`, `v₂ = (0,1)`, `v₀ = (-1,-1)`, see `Cubic.ToricHeights.supportFunction`);
  `Γ` swaps `v₁` and `v₂`, i.e. acts by `Prod.swap`.
  `𝔱^∨ = (𝔱_E^∨)^Γ` is therefore the space of real linear functionals `m` on `ℝ × ℝ`
  with `m ∘ swap = m` (`invariantDual`).
* `ℓ(x) = ½ ∑_{w} ℓ_w(x_w) log q_w` is `AdelicData.logarithm` (weights `log q_w/[E:ℚ]`), and `⟨m, ℓ(x)⟩ = m (AdelicData.logarithm x)`.
* `e(u) = Circle.exp (2π u)`.

Since a character on the quotient is determined by its pullback, `χ = χₘ` is stated as
`χ (mk x) = e(m(ℓ x))` for every adelic point `x`. The claim records both that each
`χₘ` is a well-defined automorphic character trivial on `K^{D₀}` and that every such
character is a `χₘ`; `m` is moreover unique, which is what makes `t = m(v₀)` a
coordinate on `𝔱^∨` as used right after the equation.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.ChimDefn

open Cubic.PoissonSummation
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology

/-- `𝔱^∨ = (𝔱_E^∨)^Γ`: `Γ`-invariant real linear functionals on `𝔱_E = ℝ × ℝ`. -/
def invariantDual : Submodule ℝ ((ℝ × ℝ) →ₗ[ℝ] ℝ) where
  carrier m := ∀ n : ℝ × ℝ, m n.swap = m n
  add_mem' ha hb n := by simp [ha n, hb n]
  zero_mem' n := rfl
  smul_mem' c m hm n := by simp [hm n]

/-- `χ` agrees with `χₘ(x) = e(⟨m, ℓ(x)⟩)` on every adelic point. -/
def IsChi (m : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (χ : PontryaginDual AdelicRationalCharacter.AutomorphicQuotient) : Prop :=
  ∀ x : AdelicData.Points,
    χ (QuotientGroup.mk x) = Circle.exp (2 * Real.pi * m (AdelicData.logarithm x))

/-- Triviality on the image of `K^{D₀}`. -/
def LevelTrivial (χ : PontryaginDual AdelicRationalCharacter.AutomorphicQuotient) : Prop :=
  ∀ k ∈ AdelicLevel.level, χ (QuotientGroup.mk k) = 1

structure Claim : Prop where
  /-- Each `χₘ`, `m ∈ 𝔱^∨`, is an automorphic character trivial on `K^{D₀}`. -/
  exists_character : ∀ m ∈ invariantDual,
    ∃ χ : PontryaginDual AdelicRationalCharacter.AutomorphicQuotient,
      LevelTrivial χ ∧ IsChi m χ
  /-- Every automorphic character trivial on `K^{D₀}` is `χₘ` for a unique `m ∈ 𝔱^∨`. -/
  eq_chi : ∀ χ : PontryaginDual AdelicRationalCharacter.AutomorphicQuotient,
    LevelTrivial χ → ∃! m : (ℝ × ℝ) →ₗ[ℝ] ℝ, m ∈ invariantDual ∧ IsChi m χ

end CubicTargets.PoissonSummation.ChimDefn
