import Cubic.PoissonSummation.IntegralityStabilizer

/-!
# Concrete full target for `prop:localIntegrality`

All objects are the project's fixed concrete constructions; no hypotheses are added.

* `T(ℚ_p)` is `quotientFixedRing →ₐ[ℚ] ℚ_[p]` and `T(𝔸)` is `AdelicData.Points`
  (the original real points times the restricted product over `family p`).
* `1_v^{D₀}` is `IntegralityStabilizer.localIndicatorAt` (the indicator of integrality of
  `e₂`, `e₃`, `δ`), and on adelic factors `IntegralityStabilizer.localIndicator`.
  `1^{D₀}` is `IntegralityStabilizer.globalIndicator = 1_∞ · ∏'_p 1_p^{D₀}`, with `1_∞ = 1`.
* `K_v^{max}` is `(family p).maxCompact` (proved to be the maximal compact subgroup) and
  `K^{max}` is `AdelicCompactQuotient.maximalCompact`. The stabilizers `K_v^{D₀}`, `K^{D₀}`
  and the stabilizer of `1^{D₀}` are defined as translation stabilizers
  (`IntegralityStabilizer.localStabilizer`, `productStabilizer`, `globalStabilizer`).
* `ℓ_w(x)` is `QuotientLocalCharacters.localCocharacter` for the concrete place map of `w`:
  the cocharacter determined by the `w`-adic orders of the original invariant-ring characters.
  Over a split prime the two places of `E` are the two factor projections
  `SplitQuotientLogarithm.place` and `secondPlace` of `E ⊗ ℚ_p ≅ ℚ_p × ℚ_p`; over an inert
  prime the unique place is `InertQuotientLogarithm.place` into the unramified quadratic
  extension, with its normalized order. `ℝ≥0 v₁ + ℝ≥0 v₂` is `LatticeCone.InCone`
  (both `(v₁,v₂)`-coordinates nonnegative).
* At three: `E_w` is `CyclotomicRamifiedField.Extension`, `O_{E,w}` is `integers`, and `ι₃`
  composed with the specified place `E ⊗ ℚ₃ ≅ E_w` is `RamifiedQuotientLogarithm.localPoint`.
  `K_{3,2}` is `IntegralityStabilizer.ramifiedCongruenceSet`, defined as `ι₃⁻¹(1+𝔴²)`.
-/

namespace CubicTargets.PoissonSummation.LocalIntegrality

open Cubic.QuadraticCorrespondence Cubic.ToricHeights Cubic.PoissonSummation
open CyclotomicTorusGalois IntegralityStabilizer FiniteEulerProduct QuotientFiniteFourierProduct
open CyclotomicRamifiedField (Extension integers)
open scoped TensorProduct RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

structure Claim : Prop where
  /-- (1), split prime, first place over `p`. -/
  split_first : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x)
  /-- (1), split prime, second place over `p`. -/
  split_second : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x)
  /-- (1), inert prime (including two), its unique place. -/
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
        (InertLocalModel.integerValuation p) x)
  /-- (1), "in particular": `K_v^{D₀} = K_v^{max}` for `v ≠ 3`. -/
  stabilizer_away : ∀ p : Nat.Primes, p ≠ primeThree → localStabilizer p = (family p).maxCompact
  /-- (2), setup: `𝔴 = (1-ζ)O_{E,w}` is the maximal ideal of `O_{E,w}`. -/
  maximalIdeal_eq : ∀ a : integers, a ∈ IsLocalRing.maximalIdeal integers ↔
    ∃ b : integers, (a : Extension) =
      (1 - RamifiedQuotientLogarithm.place (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[3]))) * b
  /-- (2), setup: `3 O_{E,w} = 𝔴²`. -/
  maximalIdeal_sq : IsLocalRing.maximalIdeal integers ^ 2 = Ideal.span {(3 : integers)}
  /-- (2): the support of `1_3^{D₀}` is `K_{3,2}`. -/
  support_three : Function.support (localIndicatorAt 3) = ramifiedCongruenceSet
  /-- (2): `ι₃⁻¹(1+𝔴²) = ι₃⁻¹(1+3O_{E,w})`. -/
  congruence_three : ramifiedCongruenceSet =
    {x | ∃ a : integers, ((RamifiedQuotientLogarithm.localPoint x : Extensionˣ) : Extension) =
      1 + 3 * (a : Extension)}
  /-- (2): `K_{3,2}` is a subgroup of `K_3^{max}`. -/
  subgroup_three : ∃ H : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]),
    (H : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) = ramifiedCongruenceSet ∧
      H ≤ QuotientLocalHaar.ramifiedCompactUnits
  /-- (3): `K^{D₀} ⊂ K^{max}`. -/
  product_le : productStabilizer ≤ AdelicCompactQuotient.maximalCompact
  /-- (3): `K^{D₀}` is the subgroup of `K^{max}` fixing `1^{D₀}`. -/
  product_eq_global : productStabilizer = globalStabilizer
  /-- (3): `K_3^{D₀} = K_{3,2}`. -/
  stabilizer_three : ∀ x : quotientFixedRing →ₐ[ℚ] ℚ_[3],
    x ∈ localStabilizer primeThree ↔ x ∈ ramifiedCongruenceSet
  /-- (3): `K^{D₀} = K_{3,2} × ∏_{v≠3} K_v^{max}`, with `K_∞^{max}` at infinity. -/
  product_eq : (productStabilizer : Set AdelicData.Points) =
    {x | x.1 ∈ archimedeanMaxCompact ∧
      (x.2 primeThree : quotientFixedRing →ₐ[ℚ] ℚ_[3]) ∈ ramifiedCongruenceSet ∧
      ∀ p : Nat.Primes, p ≠ primeThree → x.2 p ∈ (family p).maxCompact}
  /-- (3): the same subgroup is the level `AdelicLevel.level` used in the Poisson argument. -/
  product_eq_level : productStabilizer = AdelicLevel.level

end CubicTargets.PoissonSummation.LocalIntegrality
