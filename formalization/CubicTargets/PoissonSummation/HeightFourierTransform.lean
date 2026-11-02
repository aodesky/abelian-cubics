import CubicTargets.ToricHeights.BasicFacts
import CubicTargets.PoissonSummation.ChimDefn
import Cubic.PoissonSummation.IntegralityStabilizer
import Cubic.PoissonSummation.CharacterIntegral

/-!
# Concrete full statement of `prop:heightFourierTransform`

`s ∈ (ℂ^{Σ(1)})^Γ` is `(s₀, σ, σ)`: `Γ` swaps `v₁, v₂`, so `s₁ = s₂ = σ`.
The support function `φ` with `φ(v_e) = -s_e` is `Cubic.ToricHeights.supportFunction s₀ σ`.
So `s₁ + s₂` is written `σ + σ`, and "`Re s_e > 0` for each `e`" is `0 < s₀.re ∧ 0 < σ.re`.

## The objects (documented equivalents)

* `T(ℝ)` is `ArchimedeanQuotientLogarithm.Points`. Its measure `d^×x_∞` is
  `ArchimedeanHaar.measure`, the Haar measure normalized so that the pushforward under
  `log|·|` is `du`. It is the unique such measure (`ArchimedeanHaar.unique`).
  `K_∞^max` is `IntegralityStabilizer.archimedeanMaxCompact`, the kernel of `ℓ_w`
  (`prop:basicfacts`). `ℓ_w` is `BasicFacts.archimedeanLog`.
* `T(ℚ_p)` is `quotientFixedRing →ₐ[ℚ] ℚ_[p]`. Its measure is
  `QuotientLocalHaar.{split,inert,ramified}Measure`: Haar measure with mass one on
  `K_p^max = QuotientLocalHaar.*CompactUnits`, proved maximal compact there.
* `H_v(x,-s)` is the project's local inverse height:
  - `ArchimedeanQuotientLogarithm.inverseHeight` at infinity;
  - `QuotientFiniteHeight.{split,inert,ramified}InverseHeight` at finite places.
  These are the local components of `AdelicData.inverseHeight`
  (`AdelicData.inverseHeight_includeInfinite`, `inverseHeight_includeFinite`).
  The same function is `H_v(x,s)^{-1}` (`LocalDegreeNormalization.negative_parameters_height`).
* `1_v^{D₀}` is `IntegralityStabilizer.localIndicatorAt p`, and `1_∞^{D₀}` is
  `IntegralityStabilizer.archimedeanIndicator = 1`.
* `Ĥ_v(χ,-s,D₀) = ∫ H_v(x,-s) 1_v^{D₀}(x) χ(x)^{-1} d^×x_v` is
  `Cubic.PoissonSummation.characterIntegral`. A unitary character `χ ∈ T(ℚ_v)^∨` is an element of
  `PontryaginDual`. The integral is a Bochner integral, so absolute convergence (integrability)
  is stated separately wherever the paper uses it.
* Ramified means nontrivial on `K_v^max`; unramified means trivial on `K_v^max`.
* `𝔱^∨` and `m ∈ 𝔱^∨` are as in `eqn:chimdefn` (`ChimDefn.invariantDual`).
  `⟨ℓ_w(x), m⟩ = m (ℓ_w x)`, `v₀ = (-1,-1)`, and `e(u) = Circle.exp (2πu)`.
* Places `w | v`, `ℓ_w`, and `X_*(T_E)^{Γ(w/v)}` are those of `prop:basicfacts`
  (`BasicFacts.invariantLattice`, in integral `(v₁, ω)` coordinates). The integral cocharacters
  are named below; composing them with `cocharacterEmbedding` gives
  `BasicFacts.splitLog`, `splitSecondLog` and `inertLog`.
  `n ∈ ℝ≥0 v₁ + ℝ≥0 v₂` is `LatticeCone.InCone n`, and `φ(n)` is `φ(cocharacterEmbedding n)`.
* "Regard `χ` as a character of `X_*(T_E)^{Γ(w/v)}`" means a homomorphism
  `ψ : X_*(T_E)^{Γ(w/v)} → S¹` with `χ = ψ ∘ ℓ_w` (`Descends`). It is unique because `ℓ_w` is onto.
* `q_v` is the residue cardinality of `ℚ_p`: `Nat.card (IsLocalRing.ResidueField ℤ_[p])`.
* Holomorphy in `s` is complex (Fréchet) differentiability of `(s₀, σ) ↦ Ĥ_v` on the open
  region `{Re σ > 0}` of `ℂ²`. The region places no condition on `s₀`, as in the paper.
* At `3`: `K_{3,2}` is `IntegralityStabilizer.ramifiedCongruenceSet`. `ι₃` composed with the
  place of `E` over `3` is `RamifiedQuotientLogarithm.localPoint`, with values in
  `E_wˣ = CyclotomicRamifiedField.Extensionˣ`, and `O_{E,w}` is `CyclotomicRamifiedField.integers`.
  The index is `Subgroup.relIndex`.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.HeightFourierTransform

open MeasureTheory
open Cubic.QuadraticCorrespondence Cubic.ToricHeights Cubic.PoissonSummation
open Cubic.OrbitParametrization
open CyclotomicTorusGalois QuotientLocalCharacters IntegralityStabilizer
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.ChimDefn (invariantDual)
open CyclotomicRamifiedField (Extension integers)
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  ArchimedeanHaarData QuotientLocalHaar

/-! ### The infinite place -/

/-- `x ↦ H_∞(x,-s,D₀) = H_∞(x,-s) 1_∞^{D₀}(x)` on `T(ℝ)`. -/
def infiniteIntegrand (s₀ σ : ℂ) (x : ArchimedeanQuotientLogarithm.Points) : ℂ :=
  ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x * (archimedeanIndicator x : ℂ)

/-- `Ĥ_∞(χ,-s,D₀)`. -/
def infiniteFourier (s₀ σ : ℂ) (χ : PontryaginDual ArchimedeanQuotientLogarithm.Points) : ℂ :=
  characterIntegral ArchimedeanHaar.measure (infiniteIntegrand s₀ σ) χ

/-- `χ(x) = e(⟨ℓ_w(x), m⟩)` for all `x ∈ T(ℝ)`. -/
def IsExponential (m : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (χ : PontryaginDual ArchimedeanQuotientLogarithm.Points) : Prop :=
  ∀ x, χ x = Circle.exp (2 * Real.pi * m (archimedeanLog x))

/-- The right side of `eqn:infiniteHeightFourierTransform`, with `s₁ = s₂ = σ`. -/
def infiniteFormula (s₀ σ : ℂ) (m : (ℝ × ℝ) →ₗ[ℝ] ℝ) : ℂ :=
  (-1 / (2 * Real.pi * Complex.I)) * ((s₀ + σ + σ) / (2 * Real.pi * Complex.I)) *
    (1 / (((m (-1, -1) : ℝ) + s₀ / (2 * Real.pi * Complex.I)) *
      ((m (-1, -1) : ℝ) - (σ + σ) / (2 * Real.pi * Complex.I))))

/-! ### Finite places -/

/-- `q_v` for `v = p`. -/
abbrev residueCard (p : ℕ) [Fact p.Prime] : ℕ := Nat.card (IsLocalRing.ResidueField ℤ_[p])

/-- `ℓ_w` at the first split place, in integral coordinates. -/
abbrev splitCochar (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℤ × ℤ :=
  localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p) (PadicMultiplicative.valuation p) x

/-- `ℓ_w` at the second split place, in integral coordinates. -/
abbrev splitSecondCochar (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℤ × ℤ :=
  localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p) (PadicMultiplicative.valuation p) x

/-- `ℓ_w` at the inert place, in integral coordinates. -/
abbrev inertCochar (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℤ × ℤ :=
  localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
    (InertLocalModel.integerValuation p) x

/-- `x ↦ H_p(x,-s,D₀)` at a split prime. -/
def splitIntegrand (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (s₀ σ : ℂ)
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  QuotientFiniteHeight.splitInverseHeight p s₀ σ x * (localIndicatorAt p x : ℂ)

/-- `x ↦ H_p(x,-s,D₀)` at an inert prime. -/
def inertIntegrand (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (s₀ σ : ℂ)
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  QuotientFiniteHeight.inertInverseHeight p s₀ σ x * (localIndicatorAt p x : ℂ)

/-- `x ↦ H_3(x,-s,D₀)`. -/
def ramifiedIntegrand (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℂ :=
  QuotientFiniteHeight.ramifiedInverseHeight s₀ σ x * (localIndicatorAt 3 x : ℂ)

/-- `Ĥ_p(χ,-s,D₀)` at a split prime. -/
def splitFourier (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (s₀ σ : ℂ)
    (χ : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[p])) : ℂ :=
  characterIntegral (QuotientLocalHaar.splitMeasure p) (splitIntegrand p s₀ σ) χ

/-- `Ĥ_p(χ,-s,D₀)` at an inert prime. -/
def inertFourier (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (s₀ σ : ℂ)
    (χ : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[p])) : ℂ :=
  characterIntegral (QuotientLocalHaar.inertMeasure p) (inertIntegrand p s₀ σ) χ

/-- `Ĥ_3(χ,-s,D₀)`. -/
def ramifiedFourier (s₀ σ : ℂ) (χ : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[3])) : ℂ :=
  characterIntegral QuotientLocalHaar.ramifiedMeasure (ramifiedIntegrand s₀ σ) χ

/-- For every unitary `χ`, the integral defining `Ĥ_v(χ,-s,D₀)` converges absolutely on
`{Re σ > 0}`, and is holomorphic in `s = (s₀, σ)` there. -/
def ConvergesHolomorphically {G : Type} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) (f : ℂ → ℂ → G → ℂ) : Prop :=
  ∀ χ : PontryaginDual G,
    (∀ s₀ σ : ℂ, 0 < σ.re → Integrable (fun x => f s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) μ) ∧
      DifferentiableOn ℂ (fun s : ℂ × ℂ => characterIntegral μ (f s.1 s.2) χ) {s | 0 < s.2.re}

/-- `χ = ψ ∘ ℓ_w`: `χ` regarded as the character `ψ` of `X_*(T_E)^{Γ(w/v)}`. -/
def Descends {G : Type} [CommGroup G] [TopologicalSpace G] (D : DecompositionGroup)
    (ℓ : G → ℤ × ℤ) (χ : PontryaginDual G) (ψ : Multiplicative (invariantLattice D) →* Circle) :
    Prop :=
  ∀ (x : G) (n : invariantLattice D), (n : ℤ × ℤ) = ℓ x → χ x = ψ (Multiplicative.ofAdd n)

/-- The terms of the right side of `eqn:finiteHeightFourierTransform`, indexed by
`n ∈ X_*(T_E)^{Γ(w/v)}` with `n ∈ ℝ≥0 v₁ + ℝ≥0 v₂`. -/
def coneTerm (D : DecompositionGroup) (q : ℕ) (s₀ σ : ℂ)
    (ψ : Multiplicative (invariantLattice D) →* Circle)
    (n : {n : invariantLattice D // LatticeCone.InCone n}) : ℂ :=
  ((ψ (Multiplicative.ofAdd n.1) : Circle) : ℂ)⁻¹ *
    (q : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding n.1)

/-- The conclusions at a place `w` over `v ≠ 3`, given `K_v^max`, `Γ(w/v)`, `ℓ_w`, `q_v` and
`χ ↦ Ĥ_v(χ,-s,D₀)`. -/
structure PlaceConclusions {G : Type} [CommGroup G] [TopologicalSpace G] (K : Subgroup G)
    (D : DecompositionGroup) (ℓ : G → ℤ × ℤ) (q : ℕ)
    (F : ℂ → ℂ → PontryaginDual G → ℂ) : Prop where
  /-- Ramified `χ`: `Ĥ_v(χ,-s,D₀) = 0`. -/
  ramified : ∀ χ : PontryaginDual G, (∃ k ∈ K, χ k ≠ 1) →
    ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re → F s₀ σ χ = 0
  /-- Unramified `χ` is a character of `X_*(T_E)^{Γ(w/v)}`. -/
  descends : ∀ χ : PontryaginDual G, (∀ k ∈ K, χ k = 1) →
    ∃! ψ : Multiplicative (invariantLattice D) →* Circle, Descends D ℓ χ ψ
  /-- `eqn:finiteHeightFourierTransform`, including convergence of the sum. -/
  formula : ∀ χ : PontryaginDual G, (∀ k ∈ K, χ k = 1) →
    ∀ ψ, Descends D ℓ χ ψ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
      HasSum (coneTerm D q s₀ σ ψ) (F s₀ σ χ)

structure Claim : Prop where
  /-- Infinity: the integral converges absolutely. -/
  infinite_integrable : ∀ (χ : PontryaginDual ArchimedeanQuotientLogarithm.Points) (s₀ σ : ℂ),
    0 < s₀.re → 0 < σ.re →
      Integrable (fun x => infiniteIntegrand s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) ArchimedeanHaar.measure
  /-- Infinity: ramified `χ` gives `Ĥ_∞(χ,-s,D₀) = 0`. -/
  infinite_ramified : ∀ χ : PontryaginDual ArchimedeanQuotientLogarithm.Points,
    (∃ k ∈ archimedeanMaxCompact, χ k ≠ 1) →
      ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re → infiniteFourier s₀ σ χ = 0
  /-- Infinity: unramified `χ` is `e(⟨ℓ_w(·), m⟩)` for a unique `m ∈ 𝔱^∨`. -/
  infinite_unramified : ∀ χ : PontryaginDual ArchimedeanQuotientLogarithm.Points,
    (∀ k ∈ archimedeanMaxCompact, χ k = 1) →
      ∃! m : (ℝ × ℝ) →ₗ[ℝ] ℝ, m ∈ invariantDual ∧ IsExponential m χ
  /-- Infinity: `eqn:infiniteHeightFourierTransform`. -/
  infinite_formula : ∀ (χ : PontryaginDual ArchimedeanQuotientLogarithm.Points)
    (m : (ℝ × ℝ) →ₗ[ℝ] ℝ), (∀ k ∈ archimedeanMaxCompact, χ k = 1) → m ∈ invariantDual →
      IsExponential m χ → ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
        infiniteFourier s₀ σ χ = infiniteFormula s₀ σ m
  /-- Every finite `v`: convergence and holomorphy. Split primes. -/
  split_converges : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    ConvergesHolomorphically (QuotientLocalHaar.splitMeasure p) (splitIntegrand p)
  /-- Every finite `v`: convergence and holomorphy. Inert primes. -/
  inert_converges : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)],
    ConvergesHolomorphically (QuotientLocalHaar.inertMeasure p) (inertIntegrand p)
  /-- Every finite `v`: convergence and holomorphy. `v = 3`. -/
  three_converges : ConvergesHolomorphically QuotientLocalHaar.ramifiedMeasure ramifiedIntegrand
  /-- `v ≠ 3` split: `1_v^{D₀}` is `K_v^max`-invariant. -/
  split_invariant : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    ∀ k ∈ QuotientLocalHaar.splitCompactUnits p, ∀ x, localIndicatorAt p (x * k) = localIndicatorAt p x
  /-- `v ≠ 3` inert: `1_v^{D₀}` is `K_v^max`-invariant. -/
  inert_invariant : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)],
    ∀ k ∈ QuotientLocalHaar.inertCompactUnits p, ∀ x, localIndicatorAt p (x * k) = localIndicatorAt p x
  /-- `v ≠ 3` split, first place `w`. -/
  split_first : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    PlaceConclusions (QuotientLocalHaar.splitCompactUnits p) .trivial (splitCochar p)
      (residueCard p) (splitFourier p)
  /-- `v ≠ 3` split, second place `w`. -/
  split_second : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    PlaceConclusions (QuotientLocalHaar.splitCompactUnits p) .trivial (splitSecondCochar p)
      (residueCard p) (splitFourier p)
  /-- `v ≠ 3` inert, its place `w`. -/
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)],
    PlaceConclusions (QuotientLocalHaar.inertCompactUnits p) .whole (inertCochar p)
      (residueCard p) (inertFourier p)
  /-- `v = 3`: the support of `H_3(·,-s,D₀)` is `K_{3,2}`. -/
  three_support : ∀ s₀ σ : ℂ, 0 < s₀.re → 0 < σ.re →
    Function.support (ramifiedIntegrand s₀ σ) = ramifiedCongruenceSet
  /-- `v = 3`: `K_{3,2}` is a subgroup of `K_3^max` of index six. -/
  three_index : ∃ H : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]),
    (H : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) = ramifiedCongruenceSet ∧
      H ≤ QuotientLocalHaar.ramifiedCompactUnits ∧
      H.relIndex QuotientLocalHaar.ramifiedCompactUnits = 6
  /-- `v = 3`: under `ι₃`, the support is `1 + 3O_{E,w} ⊆ O_{E,w}^×`. -/
  three_image : RamifiedQuotientLogarithm.localPoint '' ramifiedCongruenceSet =
    {u : Extensionˣ | ∃ a : integers, (u : Extension) = 1 + 3 * (a : Extension)} ∧
      ∀ u ∈ RamifiedQuotientLogarithm.localPoint '' ramifiedCongruenceSet,
        (u : Extension) ∈ integers ∧ ((u⁻¹ : Extensionˣ) : Extension) ∈ integers

end CubicTargets.PoissonSummation.HeightFourierTransform
