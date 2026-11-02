import Cubic.QuadraticCorrespondence.QuotientLocalTopology
import Cubic.ToricHeights.SplitQuotientLogarithm
import Cubic.ToricHeights.InertQuotientLogarithm
import Cubic.ToricHeights.RamifiedQuotientLogarithm
import Cubic.ToricHeights.ArchimedeanQuotientLogarithm

/-!
# Concrete full statement of `prop:basicfacts`

For every place `w` of `E = ℚ(√-3)` over a place `v` of `ℚ`:
`1 → K_v^max → T(ℚ_v) →^{ℓ_w} t_w` is exact; `ℓ_w` is onto `t_w` if `w` is
infinite; and its image is `X_*(T_E)^{Γ(w/v)}` if `w` is finite.

## Documented equivalents (modelling of the paper's objects)

* `T(ℚ_v)` is the group of `ℚ_v`-points of the descended cyclic-invariant
  coordinate ring, `quotientFixedRing →ₐ[ℚ] ℚ_v`, with the descended group law
  (`RationalQuotientGroup`) and the topology of regular-function evaluation
  (`RegularFunctionTopology`, `QuotientLocalTopology`).
* `t_E = N_E ⊗ ℝ` is `ℝ × ℝ` in the ambient ray coordinates `(v₁, v₂)`;
  `N_E` sits in it through `cocharacterEmbedding` (integral `(v₁, ω)`
  coordinates, `CocharacterLattice.coordinates`). `γ` acts on `N_E` by
  `CocharacterLattice.conjugation` and on `t_E` by the swap, compatibly
  (`CocharacterLattice.coordinates_conjugation`).
* `K_v^max`, "the maximal compact subgroup of `T(ℚ_v)`", enters only through
  its defining property: exactness at `T(ℚ_v)` is stated as "the kernel of
  `ℓ_w` is a compact subgroup containing every compact subgroup", i.e. the
  kernel *is* the maximal compact subgroup. Exactness at `K_v^max` (injectivity
  of an inclusion) carries no content.
* Places. Every rational prime is `3` or `≡ 1, 2 (mod 3)`, and the places of
  `E` are represented by the project's concrete place maps out of
  `E ⊗ ℚ_v`, with their normalized (surjective onto `ℤ`) valuations `ord_w`:
  - `v = ∞`: the complex place `CyclotomicArchimedean.place`,
    with `ord_w = -log|·|` (`ArchimedeanQuotientLogarithm.order`, the
    normalization `q_w = e²`, `‖z‖_w = |z|²`);
  - `p ≡ 1 (mod 3)`: the two places `SplitQuotientLogarithm.place` and
    `secondPlace` (the two factors of `E ⊗ ℚ_p ≅ ℚ_p × ℚ_p`), with
    `ord_w = Padic.valuation`;
  - `p ≡ 2 (mod 3)`: the inert place `InertQuotientLogarithm.place`;
  - `p = 3`: the ramified place `RamifiedQuotientLogarithm.place`, with
    `ord_w(ζ - 1) = 1`.
  The identification of these place maps with the completions `E_w` of the
  number field `E` at its places is not formalized; it is the standard
  description of `E ⊗ ℚ_v` as the product of completions.
* Decomposition groups. The tag `.trivial`/`.whole` attached to each place
  is certified inside `Claim` (fields `*_decomposition`):
  at a split prime both place maps are `ℚ_p`-algebra maps, conjugation of `E`
  carries the first to the second, and they differ, so `γ ∉ Γ(w/v)` and
  `t_w = t_E`, `X_*(T_E)^{Γ(w/v)} = N_E`; at the inert, ramified and complex
  places the place map is `ℚ_v`-linear and conjugation of `E` acts on the
  completion through a norm-preserving automorphism, so `Γ(w/v) = Γ`.
* `ℓ_w(x)` is the element of `t_E` whose pairing with every character
  `χ^m` (`m ∈ M_E`) is `ord_w(χ^m(x))`. It is realized by
  `QuotientLocalCharacters.localCocharacter` (finite places; defining pairing
  and uniqueness: `localCocharacter_pairing`, `localCocharacter_unique`) and
  `ArchimedeanQuotientLogarithm.localCocharacter` (complex place; same two
  lemmas there). No formula for the image or the kernel is built in.

## Proof route

The proof follows the paper: the general argument of [MR291099, (1.3)]
(the Hom description `T(ℚ_v) = Hom_{Γ(w/v)}(M_E, E_w^×)`, `ℓ_w = ord_w ∘ ·`,
kernel `Hom_{Γ(w/v)}(M_E, O_w^×) = K_v^max`, image via a `Γ(w/v)`-fixed
section of `ord_w`) at every place except for the image at the ramified place,
where the paper's diagram is used: the isomorphism `eqn:isoCocharLattices`,
the coinduced module `Hom(M_E', O_w^×)` and Shapiro's lemma
(`groupCohomology.coindIso`). The proof file `Cubic.ToricHeights.BasicFacts`
records the correspondence with the paper's proof.
-/

noncomputable section

namespace CubicTargets.ToricHeights.BasicFacts

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois QuotientLocalCharacters
open Cubic.OrbitParametrization
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open scoped TensorProduct RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

/-- `N_E ↪ t_E`: integral `(v₁, ω)` coordinates to real ray coordinates `(v₁, v₂)`. -/
def cocharacterEmbedding : (ℤ × ℤ) →+ ℝ × ℝ where
  toFun n := (((CocharacterLattice.coordinates n).1 : ℚ), ((CocharacterLattice.coordinates n).2 : ℚ))
  map_zero' := by simp
  map_add' n m := by simp

/-- The decomposition group `Γ(w/v) ⊆ Γ = {1, γ}`: trivial or all of `Γ`. -/
inductive DecompositionGroup
  | trivial
  | whole

/-- `t_w = t_E^{Γ(w/v)}`, with `γ` acting on ray coordinates by the swap. -/
def invariantSpace : DecompositionGroup → AddSubgroup (ℝ × ℝ)
  | .trivial => ⊤
  | .whole =>
    { carrier := {x | x.swap = x}
      zero_mem' := rfl
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, Prod.swap_add] at hx hy ⊢
        rw [hx, hy]
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, Prod.swap_neg] at hx ⊢
        rw [hx] }

/-- `X_*(T_E)^{Γ(w/v)} = N_E^{Γ(w/v)}` in integral coordinates. -/
def invariantLattice : DecompositionGroup → AddSubgroup (ℤ × ℤ)
  | .trivial => ⊤
  | .whole => CocharacterLattice.invariantLattice

/-- Exactness of `1 → K_v^max → T(ℚ_v) → t_w` for a map `ℓ : T(ℚ_v) → t_E`:
`ℓ` is a homomorphism into `t_w`, and its kernel is the maximal compact subgroup. -/
structure ExactSequence {G : Type*} [Group G] [TopologicalSpace G] (ℓ : G → ℝ × ℝ)
    (D : DecompositionGroup) : Prop where
  map_mul : ∀ x y, ℓ (x * y) = ℓ x + ℓ y
  mapsTo : ∀ x, ℓ x ∈ invariantSpace D
  isCompact_ker : IsCompact {x | ℓ x = 0}
  compact_subgroup_le_ker : ∀ L : Subgroup G, IsCompact (L : Set G) → ∀ x ∈ L, ℓ x = 0

/-- The finite-place conclusions: exactness, and image equal to `X_*(T_E)^{Γ(w/v)}`. -/
structure FiniteFacts {G : Type*} [Group G] [TopologicalSpace G] (ℓ : G → ℝ × ℝ)
    (D : DecompositionGroup) : Prop where
  exact : ExactSequence ℓ D
  range_eq : Set.range ℓ = cocharacterEmbedding '' (invariantLattice D : Set (ℤ × ℤ))

/-- `ℓ_w` at the first split place over `p`. -/
def splitLog (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  cocharacterEmbedding (localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
    (PadicMultiplicative.valuation p) P)

/-- `ℓ_w` at the second split place over `p`. -/
def splitSecondLog (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  cocharacterEmbedding (localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p)
    (PadicMultiplicative.valuation p) P)

/-- `ℓ_w` at the inert place over `p`. -/
def inertLog (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  cocharacterEmbedding (localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
    (InertLocalModel.integerValuation p) P)

/-- `ℓ_w` at the ramified place over `3`. -/
def ramifiedLog (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℝ × ℝ :=
  cocharacterEmbedding (localCocharacter ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom
    RamifiedLocalModel.integerValuation P)

/-- `ℓ_w` at the complex place. -/
def archimedeanLog (P : ArchimedeanQuotientLogarithm.Points) : ℝ × ℝ :=
  ArchimedeanQuotientLogarithm.localCocharacter P

structure Claim : Prop where
  /-- `w` complex, `Γ(w/v) = Γ`: exactness and surjectivity onto `t_w`. -/
  archimedean : ExactSequence archimedeanLog .whole ∧
    Set.range archimedeanLog = (invariantSpace .whole : Set (ℝ × ℝ))
  /-- `p ≡ 1 (mod 3)`: both places, `Γ(w/v)` trivial. -/
  split : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    FiniteFacts (splitLog p) .trivial ∧ FiniteFacts (splitSecondLog p) .trivial
  /-- `p ≡ 2 (mod 3)`: the inert place, `Γ(w/v) = Γ`. -/
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)],
    FiniteFacts (inertLog p) .whole
  /-- `p = 3`: the ramified place, `Γ(w/v) = Γ`. -/
  ramified : FiniteFacts ramifiedLog .whole
  /-- `Γ(w/v) = Γ` at the complex place: the place is `ℝ`-linear and conjugation
  of `E` acts on the completion `ℂ` as complex conjugation. -/
  archimedean_decomposition :
    (∀ a : ℝ, CyclotomicArchimedean.place ((1 : E) ⊗ₜ[ℚ] a) = (a : ℂ)) ∧
      ∀ x : E ⊗[ℚ] ℝ, CyclotomicArchimedean.place (baseChangeConjugation ℝ x) =
        star (CyclotomicArchimedean.place x)
  /-- `Γ(w/v)` trivial at a split prime: the two places are `ℚ_p`-algebra maps,
  conjugation of `E` carries the first place to the second, and they differ. -/
  split_decomposition : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)],
    (∀ a : ℚ_[p], SplitQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a) = a ∧
        SplitQuotientLogarithm.secondPlace p ((1 : E) ⊗ₜ[ℚ] a) = a) ∧
      (∀ x : E ⊗[ℚ] ℚ_[p], SplitQuotientLogarithm.secondPlace p x =
        SplitQuotientLogarithm.place p (baseChangeConjugation ℚ_[p] x)) ∧
      SplitQuotientLogarithm.place p ≠ SplitQuotientLogarithm.secondPlace p
  /-- `Γ(w/v) = Γ` at an inert prime: the place is `ℚ_p`-linear and conjugation
  of `E` acts on the completion through a norm-preserving automorphism. -/
  inert_decomposition : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)],
    (∀ a : ℚ_[p], InertQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a) =
        algebraMap ℚ_[p] (CyclotomicInertField.Extension p) a) ∧
      (∀ y, ‖CyclotomicInertField.conjugation p y‖ = ‖y‖) ∧
      ∀ x : E ⊗[ℚ] ℚ_[p], InertQuotientLogarithm.place p (baseChangeConjugation ℚ_[p] x) =
        CyclotomicInertField.conjugation p (InertQuotientLogarithm.place p x)
  /-- `Γ(w/v) = Γ` at the ramified prime, as at the inert primes. -/
  ramified_decomposition :
    (∀ a : ℚ_[3], RamifiedQuotientLogarithm.place ((1 : E) ⊗ₜ[ℚ] a) =
        algebraMap ℚ_[3] CyclotomicRamifiedField.Extension a) ∧
      (∀ y, ‖CyclotomicRamifiedField.conjugation y‖ = ‖y‖) ∧
      ∀ x : E ⊗[ℚ] ℚ_[3], RamifiedQuotientLogarithm.place (baseChangeConjugation ℚ_[3] x) =
        CyclotomicRamifiedField.conjugation (RamifiedQuotientLogarithm.place x)

end CubicTargets.ToricHeights.BasicFacts
