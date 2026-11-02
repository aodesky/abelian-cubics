import CubicTargets.ToricHeights.BasicFacts
import Cubic.ToricHeights.QuotientLocalHaar
import Cubic.PoissonSummation.ArchimedeanHaar
import Cubic.QuadraticCorrespondence.IsoCocharLattices
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Proof of `prop:basicfacts`

The proof follows the paper's proof of `prop:basicfacts`.

## The cited source

The paper cites [MR291099, (1.3), p. 449] (P. K. J. Draxl, *L-Funktionen
algebraischer Tori*, J. Number Theory 3 (1971) 444–467) for everything except
the image at the ramified place. The Lean proof does not rely on the cited
source; it uses the standard argument for that statement, as described in the
paper's own setup: for a torus
split by `E_w`, `T(ℚ_v) = Hom_{Γ(w/v)}(M_E, E_w^×)` by evaluating characters,
`ℓ_w` is post-composition with `ord_w`, its kernel is
`Hom_{Γ(w/v)}(M_E, O_w^×) = K_v^max`, it lands in
`Hom_{Γ(w/v)}(M_E, ℤ) = X_*(T_E)^{Γ(w/v)}`, and a `Γ(w/v)`-fixed element of
`E_w^×` of order one (a uniformizer of `ℚ_v` when `w/v` is unramified;
`e^{-t}` at the complex place) gives, for each invariant `n`, the preimage
`n(ϖ)`. At the ramified place this only yields a finite-index image (`ord_w(3) = 2`),
which is why the paper argues differently there.

## Correspondence (paper step → Lean)

* `M_E` has the basis `(a', b')`, permuted by `γ`, whose characters take the
  values `χ^{a'}(x), χ^{b'}(x)`; an element of `Hom(M_E, U)` is the pair of
  these values (`characterPair`, built from `QuotientLocalCharacters.localCharacter`),
  and `γ` acts by the twisted swap `(x, y) ↦ (τ y, τ x)` (`twistedAct`).
  `Hom_{Γ(w/v)}(M_E, U)` is `IsEquivariantPair`; `Hom_{Γ(w/v)}(M_E, ℤ)` is
  `IsInvariantPair` (in the dual basis `(ω, γω)` of `N_E`), and
  `fromCyclotomic` converts to the target's `(v₁, ω)` coordinates
  (`fromCyclotomic_mem_invariantLattice`, `isInvariantPair_fromCyclotomic_symm`).
* `T(ℚ_v) = Hom_{Γ(w/v)}(M_E, E_w^×)`: `characterPair` lands in the invariants
  (`*_equivariant`, from the place-conjugation lemmas) and is onto them
  (`*_pair_surjective`, from the local model isomorphisms).
* `K_v^max = Hom_{Γ(w/v)}(M_E, O_w^×)`: `*_mem_compactUnits_iff`, with
  compactness and maximality `QuotientLocalHaar.*` (finite places) and
  `coordinate_eq_zero_of_compact` (complex place).
* [MR291099, (1.3)], general argument: `draxl_mapsTo` (`ℓ_w` lands in
  `t_w`), `draxl_ker` (exactness), `draxl_section` (image), assembled by
  `finiteFacts_of_hom` at finite places; used at the split, inert and complex
  places for everything, and at the ramified place for exactness.
* Ramified image, the paper's diagram (section `Diagram`, assembled in
  `ramified_diagram`):
  - upper row `𝒢₁(ℚ₃) = (E ⊗ ℚ₃)^× → Hom_{Γ(w/v)}(M_E', E_w^×) →^{ℓ_w}
    Hom_{Γ(w/v)}(M_E', ℤ)`: `coverCharacterPair` (the values of
    `χ^{v₁^∨}, χ^{v₂^∨}`, i.e. `x` and its conjugate at `w`), onto the equivariant
    pairs (`coverCharacterPair_surjective`), and `upperLog` with values in
    `N_E' = Hom(M_E', ℤ)`, realized as `coverLattice = ℤ⟨v₁, v₂⟩` (`coverCochar`);
  - lower row `T(ℚ₃) → Hom_{Γ(w/v)}(M_E, E_w^×) →^{ℓ_w} Hom_{Γ(w/v)}(M_E, ℤ)`:
    `characterPair` and `lowerLog` with values in `N_E = quotientLattice = ℤ⟨ω, γω⟩`
    (`quotientCochar`); `ramifiedLog_eq_lowerLog` checks that this is the
    proposition's `ℓ_w`;
  - vertical arrows: on points `ι_v = quotientRestrictionScalarsEquiv`; on
    `Hom(·, E_w^×)` the transpose `v₁^∨ ↦ a'`, `v₂^∨ ↦ b'`
    (`characterPair_eq_coverCharacterPair`, the character pullback of the paper's
    proof of `prop:cyclotomicParametrization`); on `Hom(·, ℤ)` the isomorphism
    `f : N_E ≃ N_E'` supplied by `IsoCocharLattices.«eqn:isoCocharLattices»`
    (`ω ↦ v₁`, `γω ↦ v₂`, `Γ`-equivariant);
  - the diagram commutes (`iso_quotientCochar` for the right square,
    `diagram_commutes` for the whole);
  - surjectivity of the upper `ℓ_w` onto `(N_E')^{Γ(w/v)}` (`upperLog_surjective`,
    via `upper_surjective`): the lift through the free module `M_E'` (the `Ext¹`
    step), the 1-cocycle `γ ↦ γφ/φ` with values in `Hom(M_E', O_w^×)`, its
    triviality (`coboundary_of_cocycle`: the untwisting `(x, y) ↦ (x, τ y)`
    identifies the module with the coinduced module `Coind_1^Γ(O_w^×)`, and
    Shapiro's lemma `groupCohomology.coindIso` gives `H¹ = H¹(1, O_w^×) = 0`),
    and the corrected invariant preimage;
  - transfer to the lower row (`ramified_diagram`): an invariant `n ∈ N_E^Γ` maps to
    an invariant `f n ∈ (N_E')^Γ` by equivariance of `f`; a preimage `x` under the
    upper `ℓ_w` gives `ι_v^{-1}(x)`, whose lower `ℓ_w` is `n` because the diagram
    commutes and `f` is injective. `ramified_image` restates this in
    `Hom_{Γ(w/v)}(M_E, E_w^×)` for `finiteFacts_of_hom`.
* The decomposition groups `Γ(w/v)`: `*_decomposition`.

## Departures from the paper

* The places of `E` are the project's concrete place maps; their identification
  with the completions `E_w` is described in the docstring of the target statement,
not formalized.
* `K_v^max` is characterized by its defining property (compact, containing every
  compact subgroup), as in the target.
* In the diagram, `Hom(M_E', ·)` and `Hom(M_E, ·)` are both written as pairs of
  values on bases permuted by `γ` (`(v₁^∨, v₂^∨)` and `(a', b')`); the transpose of
  `eqn:isoCocharLattices` matches these bases, so the middle vertical arrow is the
  identity on pairs, and its content is `characterPair_eq` (the two pairs are
  computed from `P` and from `ι_v(P)`). The paper's upper row has left-exactness
  as well; only the surjectivity of the upper `ℓ_w`, which is what the paper uses,
  is formalized for it.
* The upper row is only built at the ramified place, where the paper uses it.
-/

noncomputable section

namespace Cubic.ToricHeights.BasicFacts

open CubicTargets.ToricHeights.BasicFacts
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois QuotientLocalCharacters CyclotomicRestrictionScalars
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CocharacterLattice
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CategoryTheory groupCohomology
open scoped TensorProduct RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

/-! ### Lattice bookkeeping -/

theorem cocharacterEmbedding_injective : Function.Injective cocharacterEmbedding := by
  intro n m h
  apply coordinates_injective
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [cocharacterEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁ h₂
  exact Prod.ext (Rat.cast_injective h₁) (Rat.cast_injective h₂)

theorem cocharacterEmbedding_conjugation (n : ℤ × ℤ) :
    cocharacterEmbedding (conjugation n) = (cocharacterEmbedding n).swap := by
  simp only [cocharacterEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    coordinates_conjugation]
  rfl

theorem cocharacterEmbedding_mem_invariantSpace (D : DecompositionGroup) (n : ℤ × ℤ)
    (hn : n ∈ invariantLattice D) : cocharacterEmbedding n ∈ invariantSpace D := by
  cases D with
  | trivial => trivial
  | whole =>
    change (cocharacterEmbedding n).swap = cocharacterEmbedding n
    rw [← cocharacterEmbedding_conjugation]
    exact congrArg cocharacterEmbedding hn

/-- `Hom_{Γ(w/v)}(M, V)` for `V` with trivial action, in a basis of `M` permuted by `γ`:
all pairs if `Γ(w/v)` is trivial, the pairs fixed by the swap if `Γ(w/v) = Γ`. -/
def IsInvariantPair {V : Type*} : DecompositionGroup → V × V → Prop
  | .trivial, _ => True
  | .whole, n => n.swap = n

/-- The vertical isomorphism is `Γ`-equivariant, so it matches the invariants. -/
theorem fromCyclotomic_mem_invariantLattice (D : DecompositionGroup) (n : ℤ × ℤ)
    (hn : IsInvariantPair D n) :
    CocharacterIsomorphism.fromCyclotomic n ∈ invariantLattice D := by
  cases D with
  | trivial => trivial
  | whole =>
    change conjugation (CocharacterIsomorphism.fromCyclotomic n) = _
    rw [CocharacterIsomorphism.conjugation_fromCyclotomic]
    exact congrArg _ hn

theorem isInvariantPair_fromCyclotomic_symm (D : DecompositionGroup) (n : ℤ × ℤ)
    (hn : n ∈ invariantLattice D) :
    IsInvariantPair D (CocharacterIsomorphism.fromCyclotomic.symm n) := by
  cases D with
  | trivial => trivial
  | whole =>
    change _ = _
    apply CocharacterIsomorphism.fromCyclotomic.injective
    rw [← CocharacterIsomorphism.conjugation_fromCyclotomic, AddEquiv.apply_symm_apply]
    exact hn

/-! ### The decomposition group `Γ(w/v) = Γ = {1, γ}` and its twisted action -/

/-- `Γ = Gal(E/ℚ)`, of order two. -/
abbrev Gal := Multiplicative (ZMod 2)

/-- The nontrivial element `γ`. -/
def γ : Gal := Multiplicative.ofAdd 1

theorem gal_cases (g : Gal) : g = 1 ∨ g = γ := by
  revert g; decide

theorem γ_mul_γ : γ * γ = 1 := by decide

theorem γ_ne_one : γ ≠ 1 := by decide

section Twisted

variable {U : Type*} [CommGroup U] (τ : U ≃* U)

/-- The action of `Γ` on `Hom(M, U) = U × U` (values on a basis of `M` swapped by `γ`),
`(gφ)(m) = g(φ(g⁻¹m))`: `γ` sends `(x, y)` to `(τ y, τ x)`. -/
def twistedAct (g : Gal) : U × U →* U × U :=
  if g = 1 then MonoidHom.id _ else
    (τ.toMonoidHom.comp (MonoidHom.snd U U)).prod (τ.toMonoidHom.comp (MonoidHom.fst U U))

@[simp]
theorem twistedAct_one (q : U × U) : twistedAct τ 1 q = q := by simp [twistedAct]

@[simp]
theorem twistedAct_γ (q : U × U) : twistedAct τ γ q = (τ q.2, τ q.1) := by
  simp [twistedAct, γ_ne_one]

variable {τ}

theorem twistedAct_mul (hτ : ∀ x, τ (τ x) = x) (g h : Gal) (q : U × U) :
    twistedAct τ (g * h) q = twistedAct τ g (twistedAct τ h q) := by
  rcases gal_cases g with rfl | rfl <;> rcases gal_cases h with rfl | rfl <;>
    simp [γ_mul_γ, hτ]

/-- `Hom_{Γ(w/v)}(M, U)`: the invariants of the twisted action. -/
def IsEquivariantPair (τ : U ≃* U) : DecompositionGroup → U × U → Prop
  | .trivial, _ => True
  | .whole, q => twistedAct τ γ q = q

theorem isEquivariantPair_whole_iff (hτ : ∀ x, τ (τ x) = x) (q : U × U) :
    IsEquivariantPair τ .whole q ↔ q.2 = τ q.1 := by
  change twistedAct τ γ q = q ↔ _
  rw [twistedAct_γ]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    dsimp at h1
    rw [← h1, hτ]
  · intro h
    ext
    · dsimp; rw [h, hτ]
    · exact h.symm

end Twisted

/-! ### The general argument ([MR291099, (1.3)]) on `Hom(M_E, ·)` -/

section Draxl

variable {U V : Type*} [CommGroup U] [AddCommGroup V]

/-- `ℓ_w` on `Hom(M, U)`: post-composition with `ord_w`. -/
def valuationPair (ord : U →* Multiplicative V) (q : U × U) : V × V :=
  ((ord q.1).toAdd, (ord q.2).toAdd)

theorem valuationPair_mul (ord : U →* Multiplicative V) (q r : U × U) :
    valuationPair ord (q * r) = valuationPair ord q + valuationPair ord r := by
  simp [valuationPair]

/-- `ℓ_w` lands in `Hom_{Γ(w/v)}(M, V)`, because `ord_w` is `Γ(w/v)`-invariant. -/
theorem draxl_mapsTo {τ : U ≃* U} (ord : U →* Multiplicative V) (hord : ∀ u, ord (τ u) = ord u)
    (D : DecompositionGroup) (q : U × U) (hq : IsEquivariantPair τ D q) :
    IsInvariantPair D (valuationPair ord q) := by
  cases D with
  | trivial => trivial
  | whole =>
    change twistedAct τ γ q = q at hq
    rw [twistedAct_γ] at hq
    have h2 : τ q.1 = q.2 := congrArg Prod.snd hq
    change (valuationPair ord q).swap = valuationPair ord q
    simp only [valuationPair, Prod.swap_prod_mk, ← h2, hord]

/-- Exactness: `ℓ_w φ = 0` exactly when `φ` takes values in `O_w^× = ker ord_w`. -/
theorem draxl_ker (ord : U →* Multiplicative V) (q : U × U) :
    valuationPair ord q = 0 ↔ q.1 ∈ ord.ker ∧ q.2 ∈ ord.ker := by
  simp only [valuationPair, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, MonoidHom.mem_ker]
  rfl

/-- Image: a `Γ(w/v)`-fixed homomorphism `s` with `ord_w ∘ s = id` gives, for each
invariant `n`, the equivariant preimage `n(s) = (s n₁, s n₂)`. -/
theorem draxl_section {τ : U ≃* U} (ord : U →* Multiplicative V)
    (s : Multiplicative V →* U) (hsτ : ∀ t, τ (s t) = s t) (hs : ∀ t, ord (s t) = t)
    (D : DecompositionGroup) (n : V × V) (hn : IsInvariantPair D n) :
    IsEquivariantPair τ D (s (Multiplicative.ofAdd n.1), s (Multiplicative.ofAdd n.2)) ∧
      valuationPair ord (s (Multiplicative.ofAdd n.1), s (Multiplicative.ofAdd n.2)) = n := by
  refine ⟨?_, by simp [valuationPair, hs]⟩
  cases D with
  | trivial => trivial
  | whole =>
    change n.swap = n at hn
    change twistedAct τ γ _ = _
    rw [twistedAct_γ, hsτ, hsτ]
    have h1 : n.2 = n.1 := congrArg Prod.fst hn
    simp [h1]

end Draxl

/-! ### Shapiro's lemma for the coinduced module `Hom(M_E', O_w^×)` -/

section Shapiro

variable {O : Type} [CommGroup O] (τ : O ≃* O)

/-- `H¹(1, A) = 0`, so by Shapiro's lemma `H¹(Γ, Coind_1^Γ A) = 0`. -/
theorem subsingleton_H1_coind (A : Type) [AddCommGroup A] :
    Subsingleton (H1 (Rep.coind (⊥ : Subgroup Gal).subtype (Rep.trivial ℤ (⊥ : Subgroup Gal) A))) := by
  let e := (coindIso (Rep.trivial ℤ (⊥ : Subgroup Gal) A) 1 ≪≫ H1IsoOfIsTrivial _).toLinearEquiv
  haveI : Subsingleton (Additive (⊥ : Subgroup Gal) →+ (Rep.trivial ℤ (⊥ : Subgroup Gal) A)) := by
    constructor
    intro f g
    apply AddMonoidHom.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  exact e.toEquiv.subsingleton

/-- Untwisting `(x, y) ↦ (x, τ y)`, followed by the identification of
`O × O` with the permutation action with the coinduced module
`Coind_1^Γ O = {f : Γ → O}`, `(g f)(h) = f(h g)`. -/
def untwist (q : O × O) (h : Gal) : Additive O :=
  Additive.ofMul (if h = 1 then q.1 else τ q.2)

theorem untwist_mul (q r : O × O) : untwist τ (q * r) = untwist τ q + untwist τ r := by
  funext h
  by_cases hh : h = 1 <;> simp [untwist, hh]

theorem untwist_inv (q : O × O) : untwist τ q⁻¹ = -untwist τ q := by
  funext h
  by_cases hh : h = 1 <;> simp [untwist, hh]

/-- The untwisting is `Γ`-equivariant from the twisted action to the coinduced action. -/
theorem untwist_act (hτ : ∀ x, τ (τ x) = x) (g : Gal) (q : O × O) (h : Gal) :
    untwist τ (twistedAct τ g q) h = untwist τ q (h * g) := by
  rcases gal_cases g with rfl | rfl <;> rcases gal_cases h with rfl | rfl <;>
    simp [untwist, γ_ne_one, γ_mul_γ, hτ]

theorem untwist_injective : Function.Injective (untwist τ) := by
  intro q r hqr
  have h1 := congrFun hqr 1
  have h2 := congrFun hqr γ
  simp only [untwist, if_neg γ_ne_one] at h1 h2
  exact Prod.ext (Additive.ofMul.injective (by simpa using h1))
    (τ.injective (Additive.ofMul.injective h2))

/-- Every 1-cocycle of `Γ` with values in the twisted module `Hom(M_E', O)` is a
coboundary: the module is coinduced, and Shapiro's lemma applies. -/
theorem coboundary_of_cocycle (hτ : ∀ x, τ (τ x) = x) (c : Gal → O × O)
    (hc : ∀ g h, c (g * h) = twistedAct τ g (c h) * c g) :
    ∃ ψ : O × O, ∀ g, c g = twistedAct τ g ψ * ψ⁻¹ := by
  let A := Rep.trivial ℤ (⊥ : Subgroup Gal) (Additive O)
  let X := Rep.coind (⊥ : Subgroup Gal).subtype A
  have hmem : ∀ q : O × O,
      untwist τ q ∈ Representation.coindV (⊥ : Subgroup Gal).subtype A.ρ := by
    intro q g h
    have hg : (g : Gal) = 1 := Subgroup.mem_bot.mp g.2
    change untwist τ q ((g : Gal) * h) = untwist τ q h
    rw [hg, one_mul]
  let c' : Gal → X := fun g => ⟨_, hmem (c g)⟩
  have hc' : c' ∈ cocycles₁ X := by
    rw [mem_cocycles₁_iff]
    intro g h
    apply Subtype.ext
    funext k
    simp only [c', X, Rep.coind, Rep.of_ρ, Submodule.coe_add, Pi.add_apply]
    change untwist τ (c (g * h)) k = untwist τ (c h) (k * g) + untwist τ (c g) k
    rw [hc g h, untwist_mul, Pi.add_apply, untwist_act τ hτ]
  haveI := subsingleton_H1_coind (Additive O)
  have hzero : H1π X ⟨c', hc'⟩ = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at hzero
  obtain ⟨a, ha⟩ := hzero
  let ψ : O × O := (Additive.toMul ((a : Gal → Additive O) 1),
    τ (Additive.toMul ((a : Gal → Additive O) γ)))
  have hψ : untwist τ ψ = a := by
    funext h
    rcases gal_cases h with rfl | rfl <;> simp [untwist, ψ, γ_ne_one, hτ]
  refine ⟨ψ, fun g => untwist_injective τ ?_⟩
  have hag := congrFun ha g
  change X.ρ g a - a = c' g at hag
  have := congrArg Subtype.val hag
  simp only [c', X, Rep.coind, Rep.of_ρ, Submodule.coe_sub] at this
  change (fun k => (a : Gal → Additive O) (k * g)) - (a : Gal → Additive O) =
    untwist τ (c g) at this
  rw [← this, untwist_mul, untwist_inv, ← sub_eq_add_neg, hψ]
  funext k
  simp only [Pi.sub_apply]
  rw [untwist_act τ hτ, hψ]

end Shapiro

/-! ### Surjectivity of the upper `ℓ_w` at a ramified place -/

section Upper

variable {U : Type} [CommGroup U]

/-- `τ` restricted to `O_w^× = ker ord_w`. -/
def unitsRestrict (τ : U ≃* U) (hτ : ∀ x, τ (τ x) = x) (ord : U →* Multiplicative ℤ)
    (hord : ∀ u, ord (τ u) = ord u) : ord.ker ≃* ord.ker where
  toFun x := ⟨τ (x : U), by rw [MonoidHom.mem_ker, hord]; exact x.2⟩
  invFun x := ⟨τ (x : U), by rw [MonoidHom.mem_ker, hord]; exact x.2⟩
  left_inv x := Subtype.ext (hτ (x : U))
  right_inv x := Subtype.ext (hτ (x : U))
  map_mul' x y := Subtype.ext (map_mul τ (x : U) y)

/-- The paper's argument that the upper `ℓ_w : Hom_Γ(M_E', E_w^×) → Hom_Γ(M_E', ℤ)`
is onto: lift through the free module `M_E'`, measure the failure of equivariance
by a 1-cocycle in `Hom(M_E', O_w^×)`, and kill it with `coboundary_of_cocycle`. -/
theorem upper_surjective (τ : U ≃* U) (hτ : ∀ x, τ (τ x) = x) (ord : U →* Multiplicative ℤ)
    (hord : ∀ u, ord (τ u) = ord u) (π : U) (hπ : ord π = Multiplicative.ofAdd 1)
    (n : ℤ × ℤ) (hn : IsInvariantPair .whole n) :
    ∃ q, IsEquivariantPair τ .whole q ∧ valuationPair ord q = n := by
  change n.swap = n at hn
  have hn' : n.2 = n.1 := congrArg Prod.fst hn
  -- `Hom(M_E', E_w^×) → Hom(M_E', ℤ)` is onto since `M_E'` is free (`Ext¹ = 0`).
  let φ : U × U := (π ^ n.1, π ^ n.2)
  have hφ : valuationPair ord φ = n := by
    simp only [valuationPair, φ, map_zpow, hπ, ← ofAdd_zsmul, toAdd_ofAdd, smul_eq_mul, mul_one]
  -- The cocycle `g ↦ gφ/φ` takes values in `Hom(M_E', O_w^×)`.
  have hmem : ∀ g, (twistedAct τ g φ * φ⁻¹).1 ∈ ord.ker ∧ (twistedAct τ g φ * φ⁻¹).2 ∈ ord.ker := by
    intro g
    rcases gal_cases g with rfl | rfl
    · simp
    · simp only [twistedAct_γ, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        MonoidHom.mem_ker, map_mul, map_inv, hord, φ, map_zpow, hn']
      simp
  let τO := unitsRestrict τ hτ ord hord
  let c : Gal → ord.ker × ord.ker := fun g => (⟨_, (hmem g).1⟩, ⟨_, (hmem g).2⟩)
  let incl : ord.ker × ord.ker →* U × U := ord.ker.subtype.prodMap ord.ker.subtype
  have hincl_inj : Function.Injective incl := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hincl_act : ∀ g x, incl (twistedAct τO g x) = twistedAct τ g (incl x) := by
    intro g x
    rcases gal_cases g with rfl | rfl <;> simp [incl, τO, unitsRestrict]
  have hc_incl : ∀ g, incl (c g) = twistedAct τ g φ * φ⁻¹ := fun g => rfl
  have hc : ∀ g h, c (g * h) = twistedAct τO g (c h) * c g := by
    intro g h
    apply hincl_inj
    rw [map_mul, hincl_act, hc_incl, hc_incl, hc_incl, twistedAct_mul hτ, map_mul, map_inv]
    group
  -- Shapiro: the cocycle is a coboundary `g ↦ gψ/ψ`.
  obtain ⟨ψ, hψ⟩ := coboundary_of_cocycle τO (fun x => Subtype.ext (hτ x)) c hc
  refine ⟨φ * (incl ψ)⁻¹, ?_, ?_⟩
  · change twistedAct τ γ _ = _
    have h := congrArg incl (hψ γ)
    rw [hc_incl, map_mul, map_inv, hincl_act] at h
    rw [map_mul, map_inv]
    calc twistedAct τ γ φ * (twistedAct τ γ (incl ψ))⁻¹
        = twistedAct τ γ φ * φ⁻¹ * φ * (twistedAct τ γ (incl ψ))⁻¹ := by group
      _ = twistedAct τ γ (incl ψ) * (incl ψ)⁻¹ * φ * (twistedAct τ γ (incl ψ))⁻¹ := by rw [h]
      _ = φ * (incl ψ)⁻¹ := by
        rw [mul_comm _ (twistedAct τ γ (incl ψ))⁻¹, ← mul_assoc, ← mul_assoc, inv_mul_cancel,
          one_mul, mul_comm]
  · rw [valuationPair_mul, hφ]
    have h0 : valuationPair ord (incl ψ)⁻¹ = 0 := by
      rw [draxl_ker]
      exact ⟨ord.ker.inv_mem ψ.1.2, ord.ker.inv_mem ψ.2.2⟩
    rw [h0, add_zero]

end Upper

/-! ### `T(ℚ_v) = Hom_{Γ(w/v)}(M_E, E_w^×)` by evaluating characters -/

section CharacterPair

variable (A : Type*) [CommRing A] [Algebra ℚ A] {L : Type*} [CommRing L]
  (place : E ⊗[ℚ] A →+* L)

/-- The values `(χ^{a'}(P), χ^{b'}(P))` of the basis characters of `M_E`: the
element of `Hom(M_E, E_w^×)` determined by `P`. -/
def characterPair (P : quotientFixedRing →ₐ[ℚ] A) : Lˣ × Lˣ :=
  (localCharacter A place P (Multiplicative.ofAdd (1, 0)),
    localCharacter A place P (Multiplicative.ofAdd (0, 1)))

/-- The middle vertical arrow of the paper's diagram: `χ^{a'}, χ^{b'}` on `P` are
`χ^{v₁^∨}, χ^{v₂^∨}` on `ι_v(P)`, i.e. `ι_v(P)` and its conjugate at the place. -/
theorem characterPair_eq (P : quotientFixedRing →ₐ[ℚ] A) :
    characterPair A place P =
      (Units.map place.toMonoidHom (quotientRestrictionScalarsEquiv A P),
        Units.map place.toMonoidHom (conjugateUnit A (quotientRestrictionScalarsEquiv A P))) := by
  simp only [characterPair, localCharacter, MonoidHom.coe_comp, Function.comp_apply,
    characterValues_formula, zpow_one, zpow_zero, mul_one, one_mul]

theorem characterPair_mul (P Q : quotientFixedRing →ₐ[ℚ] A) :
    characterPair A place (P * Q) = characterPair A place P * characterPair A place Q := by
  simp only [characterPair, localCharacter, MonoidHom.coe_comp, Function.comp_apply,
    characterValues_mul, map_mul, Prod.mk_mul_mk]

/-- The character-defined cocharacter is `ord_w ∘ ·` on this element. -/
theorem basisValuations_eq_valuationPair (ord : Lˣ →* Multiplicative ℤ)
    (P : quotientFixedRing →ₐ[ℚ] A) :
    basisValuations A place ord P = valuationPair ord (characterPair A place P) := by
  rw [characterPair_eq]
  rfl

end CharacterPair

/-! ### Assembly at a finite place -/

/-- At a finite place: from the Hom description of `T(ℚ_v)` and of `K_v^max`, and
surjectivity of `ℓ_w` on `Hom_{Γ(w/v)}(M_E, E_w^×)`, the conclusions follow. -/
theorem finiteFacts_of_hom {G : Type*} [Group G] [TopologicalSpace G] {U : Type*} [CommGroup U]
    (D : DecompositionGroup) (τ : U ≃* U) (ord : U →* Multiplicative ℤ)
    (hord : ∀ u, ord (τ u) = ord u) (pair : G → U × U) (ℓ : G → ℝ × ℝ)
    (hℓ : ∀ x, ℓ x = cocharacterEmbedding
      (CocharacterIsomorphism.fromCyclotomic (valuationPair ord (pair x))))
    (hmul : ∀ x y, pair (x * y) = pair x * pair y)
    (hequiv : ∀ x, IsEquivariantPair τ D (pair x))
    (hsurj : ∀ q, IsEquivariantPair τ D q → ∃ x, pair x = q)
    (K : Subgroup G) (hK : ∀ x, x ∈ K ↔ (pair x).1 ∈ ord.ker ∧ (pair x).2 ∈ ord.ker)
    (hKc : IsCompact (K : Set G)) (hKmax : ∀ L : Subgroup G, IsCompact (L : Set G) → L ≤ K)
    (himage : ∀ n, IsInvariantPair D n →
      ∃ q, IsEquivariantPair τ D q ∧ valuationPair ord q = n) :
    FiniteFacts ℓ D := by
  have hzero : ∀ x, ℓ x = 0 ↔ x ∈ K := fun x => by
    rw [hℓ, ← map_zero cocharacterEmbedding, cocharacterEmbedding_injective.eq_iff,
      AddEquivClass.map_eq_zero_iff, draxl_ker, hK]
  have hmem : ∀ x, CocharacterIsomorphism.fromCyclotomic (valuationPair ord (pair x)) ∈
      invariantLattice D := fun x =>
    fromCyclotomic_mem_invariantLattice D _ (draxl_mapsTo ord hord D _ (hequiv x))
  refine ⟨⟨fun x y => ?_, fun x => ?_, ?_, ?_⟩, ?_⟩
  · rw [hℓ, hℓ, hℓ, hmul, valuationPair_mul, map_add, map_add]
  · rw [hℓ]
    exact cocharacterEmbedding_mem_invariantSpace D _ (hmem x)
  · have hset : {x | ℓ x = 0} = (K : Set G) := Set.ext hzero
    rw [hset]
    exact hKc
  · intro L hL x hx
    exact (hzero x).mpr (hKmax L hL hx)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, hmem x, (hℓ x).symm⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨q, hq, hqn⟩ := himage _ (isInvariantPair_fromCyclotomic_symm D n hn)
      obtain ⟨x, rfl⟩ := hsurj q hq
      exact ⟨x, by rw [hℓ, hqn, AddEquiv.apply_symm_apply]⟩

/-- The uniformizer section `k ↦ ϖ^k`. -/
def uniformizerSection {U : Type*} [CommGroup U] (ϖ : U) : Multiplicative ℤ →* U :=
  zpowersHom U ϖ

theorem uniformizerSection_apply {U : Type*} [CommGroup U] (ϖ : U) (k : Multiplicative ℤ) :
    uniformizerSection ϖ k = ϖ ^ k.toAdd := rfl

theorem ord_uniformizerSection {U : Type*} [CommGroup U] (ord : U →* Multiplicative ℤ) (ϖ : U)
    (hϖ : ord ϖ = Multiplicative.ofAdd 1) (k : Multiplicative ℤ) :
    ord (uniformizerSection ϖ k) = k := by
  rw [uniformizerSection_apply, map_zpow, hϖ, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rfl

/-! ### Split places -/

section Split

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]

theorem split_characterPair (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    characterPair ℚ_[p] (SplitQuotientLogarithm.place p) P =
      SplitQuotientLogarithm.localPoint p P := by
  rw [characterPair_eq, SplitQuotientLogarithm.mapped_conjugate]
  rfl

/-- `T(ℚ_p) = Hom(M_E, ℚ_p^×)`: every pair of values occurs. -/
theorem split_pair_surjective (q : ℚ_[p]ˣ × ℚ_[p]ˣ) :
    ∃ P, characterPair ℚ_[p] (SplitQuotientLogarithm.place p) P = q :=
  ⟨(QuotientLocalModels.splitEquiv p).symm q, by
    rw [split_characterPair, ← QuotientLocalModels.splitEquiv_apply,
      ContinuousMulEquiv.apply_symm_apply]⟩

/-- `K_p^max = Hom(M_E, ℤ_p^×)`. -/
theorem split_mem_compactUnits_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ QuotientLocalHaar.splitCompactUnits p ↔
      (characterPair ℚ_[p] (SplitQuotientLogarithm.place p) P).1 ∈
          (PadicMultiplicative.valuation p).ker ∧
        (characterPair ℚ_[p] (SplitQuotientLogarithm.place p) P).2 ∈
          (PadicMultiplicative.valuation p).ker := by
  rw [split_characterPair, PadicMultiplicative.ker_valuation, ← QuotientLocalModels.splitEquiv_apply]
  rfl

omit [Fact (p % 3 = 1)] in
/-- The uniformizer `p` of `ℚ_p`: the section of Draxl's argument. -/
theorem split_image (n : ℤ × ℤ) :
    ∃ q, IsEquivariantPair (MulEquiv.refl ℚ_[p]ˣ) .trivial q ∧
      valuationPair (PadicMultiplicative.valuation p) q = n :=
  ⟨_, draxl_section (PadicMultiplicative.valuation p)
    (uniformizerSection (PadicMultiplicative.uniformizer p)) (fun _ => rfl)
    (ord_uniformizerSection _ _ (PadicMultiplicative.valuation_uniformizer p)) .trivial n trivial⟩

theorem split_first : FiniteFacts (splitLog p) .trivial :=
  finiteFacts_of_hom .trivial (MulEquiv.refl _) (PadicMultiplicative.valuation p) (fun _ => rfl)
    (characterPair ℚ_[p] (SplitQuotientLogarithm.place p)) (splitLog p)
    (fun P => by rw [splitLog, localCocharacter, basisValuations_eq_valuationPair])
    (characterPair_mul ℚ_[p] _) (fun _ => trivial)
    (fun q _ => split_pair_surjective p q)
    (QuotientLocalHaar.splitCompactUnits p) (split_mem_compactUnits_iff p)
    (QuotientLocalHaar.isCompact_splitCompactUnits p)
    (QuotientLocalHaar.split_compact_subgroup_le p)
    (fun n _ => split_image p n)

/-- At the second place the element of `Hom(M_E, ℚ_p^×)` is the swapped pair. -/
theorem split_second_characterPair (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    characterPair ℚ_[p] (SplitQuotientLogarithm.secondPlace p) P =
      (characterPair ℚ_[p] (SplitQuotientLogarithm.place p) P).swap := by
  rw [characterPair_eq, characterPair_eq, SplitQuotientLogarithm.secondPlace_unit,
    SplitQuotientLogarithm.secondPlace_unit, conjugateUnit_involutive]
  rfl

theorem split_second : FiniteFacts (splitSecondLog p) .trivial :=
  finiteFacts_of_hom .trivial (MulEquiv.refl _) (PadicMultiplicative.valuation p) (fun _ => rfl)
    (characterPair ℚ_[p] (SplitQuotientLogarithm.secondPlace p)) (splitSecondLog p)
    (fun P => by rw [splitSecondLog, localCocharacter, basisValuations_eq_valuationPair])
    (characterPair_mul ℚ_[p] _) (fun _ => trivial)
    (fun q _ => by
      obtain ⟨P, hP⟩ := split_pair_surjective p q.swap
      exact ⟨P, by rw [split_second_characterPair, hP, Prod.swap_swap]⟩)
    (QuotientLocalHaar.splitCompactUnits p)
    (fun P => by rw [split_second_characterPair, split_mem_compactUnits_iff]; exact And.comm)
    (QuotientLocalHaar.isCompact_splitCompactUnits p)
    (QuotientLocalHaar.split_compact_subgroup_le p)
    (fun n _ => split_image p n)

/-- `Γ(w/v)` is trivial: conjugation exchanges the two (distinct) places. -/
theorem split_decomposition :
    (∀ a : ℚ_[p], SplitQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a) = a ∧
        SplitQuotientLogarithm.secondPlace p ((1 : E) ⊗ₜ[ℚ] a) = a) ∧
      (∀ x : E ⊗[ℚ] ℚ_[p], SplitQuotientLogarithm.secondPlace p x =
        SplitQuotientLogarithm.place p (baseChangeConjugation ℚ_[p] x)) ∧
      SplitQuotientLogarithm.place p ≠ SplitQuotientLogarithm.secondPlace p := by
  refine ⟨fun a => ?_, fun x => ?_, fun h => ?_⟩
  · simp [SplitQuotientLogarithm.place, SplitQuotientLogarithm.secondPlace]
  · change (SplitQuotientLogarithm.splitting p x).2 =
      (SplitQuotientLogarithm.splitting p (baseChangeConjugation ℚ_[p] x)).1
    rw [SplitQuotientLogarithm.splitting_conjugation]
    rfl
  · have hx : (SplitQuotientLogarithm.splitting p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p]))).1 =
        (SplitQuotientLogarithm.splitting p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p]))).2 :=
      congrArg (fun f : E ⊗[ℚ] ℚ_[p] →+* ℚ_[p] => f (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p]))) h
    rw [SplitQuotientLogarithm.splitting_zeta] at hx
    set r := Classical.choose (CyclotomicLocalRoots.field_root p Fact.out)
    have hr : r ^ 2 + r + 1 = 0 := Classical.choose_spec (CyclotomicLocalRoots.field_root p Fact.out)
    dsimp only at hx
    have h3 : (3 : ℚ_[p]) = 0 := by linear_combination (4 : ℚ_[p]) * hr - (2 * r + 1) * hx
    exact three_ne_zero h3

end Split

/-! ### Inert places -/

section Inert

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

/-- The local conjugation on `E_w^×`. -/
def inertτ : InertLocalModel.Points p ≃* InertLocalModel.Points p :=
  Units.mapEquiv (CyclotomicInertField.conjugation p).toMulEquiv

theorem inertτ_involutive (x : InertLocalModel.Points p) : inertτ p (inertτ p x) = x := by
  apply Units.ext
  change CyclotomicInertField.conjugation p (CyclotomicInertField.conjugation p (x : _)) = x
  obtain ⟨y, hy⟩ := (InertQuotientLogarithm.place p).surjective (x : CyclotomicInertField.Extension p)
  rw [← hy, ← InertQuotientLogarithm.place_conjugation, ← InertQuotientLogarithm.place_conjugation,
    baseChangeConjugation_involutive]

theorem inert_ord_τ (x : InertLocalModel.Points p) :
    InertLocalModel.integerValuation p (inertτ p x) = InertLocalModel.integerValuation p x :=
  congrArg Multiplicative.ofAdd (InertQuotientLogarithm.ord_conjugate p x)

theorem inert_characterPair (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom P =
      (InertQuotientLogarithm.localPoint p P, inertτ p (InertQuotientLogarithm.localPoint p P)) := by
  rw [characterPair_eq]
  exact Prod.ext rfl (InertQuotientLogarithm.mapped_conjugate p _)

theorem inert_equivariant (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    IsEquivariantPair (inertτ p) .whole
      (characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom P) := by
  rw [isEquivariantPair_whole_iff (inertτ_involutive p), inert_characterPair]

theorem inert_pair_surjective (q : InertLocalModel.Points p × InertLocalModel.Points p)
    (hq : IsEquivariantPair (inertτ p) .whole q) :
    ∃ P, characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom P = q := by
  rw [isEquivariantPair_whole_iff (inertτ_involutive p)] at hq
  refine ⟨(QuotientLocalModels.inertEquiv p).symm q.1, ?_⟩
  rw [inert_characterPair, ← QuotientLocalModels.inertEquiv_apply,
    ContinuousMulEquiv.apply_symm_apply]
  exact Prod.ext rfl hq.symm

theorem inert_mem_compactUnits_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ QuotientLocalHaar.inertCompactUnits p ↔
      (characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom P).1 ∈
          (InertLocalModel.integerValuation p).ker ∧
        (characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom P).2 ∈
          (InertLocalModel.integerValuation p).ker := by
  rw [inert_characterPair, MonoidHom.mem_ker, MonoidHom.mem_ker, inert_ord_τ, and_self,
    ← MonoidHom.mem_ker, InertLocalModel.ker_integerValuation,
    ← QuotientLocalModels.inertEquiv_apply]
  rfl

/-- `p` is a `Γ`-fixed uniformizer of the unramified extension `E_w`. -/
theorem inert_image (n : ℤ × ℤ) (hn : IsInvariantPair .whole n) :
    ∃ q, IsEquivariantPair (inertτ p) .whole q ∧
      valuationPair (InertLocalModel.integerValuation p) q = n := by
  refine ⟨_, draxl_section (InertLocalModel.integerValuation p)
    (uniformizerSection (InertLocalModel.uniformizer p)) (fun t => ?_)
    (ord_uniformizerSection _ _ (InertLocalModel.integerValuation_uniformizer p)) .whole n hn⟩
  rw [uniformizerSection_apply, map_zpow]
  congr 1
  apply Units.ext
  exact (CyclotomicInertField.conjugation p).commutes _

theorem inert : FiniteFacts (inertLog p) .whole :=
  finiteFacts_of_hom .whole (inertτ p) (InertLocalModel.integerValuation p) (inert_ord_τ p)
    (characterPair ℚ_[p] (InertQuotientLogarithm.place p).toRingHom) (inertLog p)
    (fun P => by rw [inertLog, localCocharacter, basisValuations_eq_valuationPair])
    (characterPair_mul ℚ_[p] _) (inert_equivariant p) (inert_pair_surjective p)
    (QuotientLocalHaar.inertCompactUnits p) (inert_mem_compactUnits_iff p)
    (QuotientLocalHaar.isCompact_inertCompactUnits p)
    (QuotientLocalHaar.inert_compact_subgroup_le p) (inert_image p)

theorem inert_decomposition :
    (∀ a : ℚ_[p], InertQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a) =
        algebraMap ℚ_[p] (CyclotomicInertField.Extension p) a) ∧
      (∀ y, ‖CyclotomicInertField.conjugation p y‖ = ‖y‖) ∧
      ∀ x : E ⊗[ℚ] ℚ_[p], InertQuotientLogarithm.place p (baseChangeConjugation ℚ_[p] x) =
        CyclotomicInertField.conjugation p (InertQuotientLogarithm.place p x) :=
  ⟨InertQuotientLogarithm.place_scalar p, CyclotomicInertField.norm_conjugation p,
    InertQuotientLogarithm.place_conjugation p⟩

end Inert

/-! ### The ramified place -/

section Ramified

/-- The local conjugation on `E_w^×`. -/
def ramifiedτ : RamifiedLocalModel.Points ≃* RamifiedLocalModel.Points :=
  Units.mapEquiv CyclotomicRamifiedField.conjugation.toMulEquiv

theorem ramifiedτ_involutive (x : RamifiedLocalModel.Points) : ramifiedτ (ramifiedτ x) = x := by
  apply Units.ext
  change CyclotomicRamifiedField.conjugation (CyclotomicRamifiedField.conjugation (x : _)) = x
  obtain ⟨y, hy⟩ := RamifiedQuotientLogarithm.place.surjective
    (x : CyclotomicRamifiedField.Extension)
  rw [← hy, ← RamifiedQuotientLogarithm.place_conjugation, ← RamifiedQuotientLogarithm.place_conjugation,
    baseChangeConjugation_involutive]

theorem ramified_ord_τ (x : RamifiedLocalModel.Points) :
    RamifiedLocalModel.integerValuation (ramifiedτ x) = RamifiedLocalModel.integerValuation x :=
  congrArg Multiplicative.ofAdd (RamifiedQuotientLogarithm.ord_conjugate x)

theorem ramified_characterPair (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P =
      (RamifiedQuotientLogarithm.localPoint P, ramifiedτ (RamifiedQuotientLogarithm.localPoint P)) := by
  rw [characterPair_eq]
  exact Prod.ext rfl (RamifiedQuotientLogarithm.mapped_conjugate _)

theorem ramified_equivariant (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    IsEquivariantPair ramifiedτ .whole
      (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P) := by
  rw [isEquivariantPair_whole_iff ramifiedτ_involutive, ramified_characterPair]

theorem ramified_pair_surjective (q : RamifiedLocalModel.Points × RamifiedLocalModel.Points)
    (hq : IsEquivariantPair ramifiedτ .whole q) :
    ∃ P, characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P = q := by
  rw [isEquivariantPair_whole_iff ramifiedτ_involutive] at hq
  refine ⟨QuotientLocalModels.ramifiedEquiv.symm q.1, ?_⟩
  rw [ramified_characterPair, ← QuotientLocalModels.ramifiedEquiv_apply,
    ContinuousMulEquiv.apply_symm_apply]
  exact Prod.ext rfl hq.symm

theorem ramified_mem_compactUnits_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    P ∈ QuotientLocalHaar.ramifiedCompactUnits ↔
      (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P).1 ∈
          RamifiedLocalModel.integerValuation.ker ∧
        (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P).2 ∈
          RamifiedLocalModel.integerValuation.ker := by
  rw [ramified_characterPair, MonoidHom.mem_ker, MonoidHom.mem_ker, ramified_ord_τ, and_self,
    ← MonoidHom.mem_ker, RamifiedLocalModel.ker_integerValuation,
    ← QuotientLocalModels.ramifiedEquiv_apply]
  rfl

theorem integerValuation_ramifiedParameter :
    RamifiedLocalModel.integerValuation RamifiedLocalModel.ramifiedParameter =
      Multiplicative.ofAdd 1 :=
  congrArg Multiplicative.ofAdd RamifiedLocalModel.ord_ramifiedParameter

/-! #### The paper's diagram at the ramified place

Upper row: `𝒢₁(ℚ₃) = (E ⊗ ℚ₃)^× → Hom_{Γ(w/v)}(M_E', E_w^×) →^{ℓ_w} Hom_{Γ(w/v)}(M_E', ℤ)`,
with `Hom(M_E', ℤ) = N_E' = coverLattice` (the basis `(v₁, v₂)` dual to `(v₁^∨, v₂^∨)`).
Lower row: `T(ℚ₃) → Hom_{Γ(w/v)}(M_E, E_w^×) →^{ℓ_w} Hom_{Γ(w/v)}(M_E, ℤ)`, with
`Hom(M_E, ℤ) = N_E = quotientLattice` (the basis `(ω, γω)` dual to `(a', b')`).
The vertical arrows are `ι_v` on points, the transpose `v₁^∨ ↦ a'`, `v₂^∨ ↦ b'` on the
`Hom(M, E_w^×)` level (`characterPair_eq`), and the isomorphism `N_E ≅ N_E'` of
`eqn:isoCocharLattices` on the right. -/

section Diagram

open CubicTargets.QuadraticCorrespondence.IsoCocharLattices (quotientLattice coverLattice gamma)

theorem omega_mem_quotientLattice : ω ∈ quotientLattice := by
  rw [IsoCocharLattices.«eqn:isoCocharLattices».quotient_span]
  exact Submodule.subset_span (by simp)

theorem gamma_omega_mem_quotientLattice : gamma ω ∈ quotientLattice := by
  rw [IsoCocharLattices.«eqn:isoCocharLattices».quotient_span]
  exact Submodule.subset_span (by simp)

/-- `Hom(M_E, ℤ) = N_E`: the cocharacter pairing to `k₁, k₂` with the basis `(a', b')`
of `M_E`, i.e. `k₁ ω + k₂ γω`. -/
def quotientCochar (k : ℤ × ℤ) : quotientLattice :=
  k.1 • ⟨ω, omega_mem_quotientLattice⟩ + k.2 • ⟨gamma ω, gamma_omega_mem_quotientLattice⟩

theorem coe_quotientCochar (k : ℤ × ℤ) :
    (quotientCochar k : ℚ × ℚ) = k.1 • ω + k.2 • gamma ω := rfl

/-- `(ω, γω)` is a basis of `N_E` (`eqn:isoCocharLattices`), so the coordinates are unique. -/
theorem quotientCochar_injective : Function.Injective quotientCochar := by
  intro k k' h
  have h' : (k.1 - k'.1) • ω + (k.2 - k'.2) • gamma ω = 0 := by
    have hv := congrArg Subtype.val h
    rw [coe_quotientCochar, coe_quotientCochar] at hv
    rw [sub_smul, sub_smul, sub_add_sub_comm, hv, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp
    IsoCocharLattices.«eqn:isoCocharLattices».quotient_independent _ _ h'
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

/-- `Hom(M_E', ℤ) = N_E'`: the cocharacter pairing to `k₁, k₂` with `(v₁^∨, v₂^∨)`,
i.e. `k₁ v₁ + k₂ v₂`. -/
def coverCochar (k : ℤ × ℤ) : coverLattice :=
  ⟨k.1 • v₁ + k.2 • v₂, Submodule.mem_span_pair.mpr ⟨k.1, k.2, rfl⟩⟩

/-- The element of `Hom(M_E', E_w^×)` determined by `x ∈ 𝒢₁(ℚ₃) = (E ⊗ ℚ₃)^×`: the values
`χ^{v₁^∨}(x), χ^{v₂^∨}(x)`, i.e. `x` and its conjugate at the place `w`. -/
def coverCharacterPair (x : (E ⊗[ℚ] ℚ_[3])ˣ) :
    RamifiedLocalModel.Points × RamifiedLocalModel.Points :=
  (Units.map RamifiedQuotientLogarithm.place.toMonoidHom x,
    Units.map RamifiedQuotientLogarithm.place.toMonoidHom (conjugateUnit ℚ_[3] x))

/-- The upper `ℓ_w : 𝒢₁(ℚ₃) → N_E'`, post-composition with `ord_w`. -/
def upperLog (x : (E ⊗[ℚ] ℚ_[3])ˣ) : coverLattice :=
  coverCochar (valuationPair RamifiedLocalModel.integerValuation (coverCharacterPair x))

/-- The lower `ℓ_w : T(ℚ₃) → N_E`, post-composition with `ord_w`. -/
def lowerLog (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : quotientLattice :=
  quotientCochar (valuationPair RamifiedLocalModel.integerValuation
    (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P))

/-- The lower row's `ℓ_w` is the proposition's `ℓ_w` (`ramifiedLog`), with
`N_E ⊆ N_{E,ℚ}'` embedded in `t_E`. -/
theorem ramifiedLog_eq_lowerLog (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedLog P = ((((lowerLog P : ℚ × ℚ).1 : ℚ) : ℝ), (((lowerLog P : ℚ × ℚ).2 : ℚ) : ℝ)) := by
  rw [ramifiedLog, localCocharacter, basisValuations_eq_valuationPair]
  simp only [cocharacterEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    CocharacterIsomorphism.coordinates_fromCyclotomic, lowerLog, coe_quotientCochar]
  simp only [ω, gamma, LinearEquiv.prodComm_apply, Prod.swap_prod_mk, Prod.smul_mk,
    Prod.fst_add, Prod.snd_add, zsmul_eq_mul]
  congr 1 <;> push_cast <;> ring

/-- The middle vertical arrow: `χ^{v₁^∨}, χ^{v₂^∨}` pull back along `ι_v` to
`χ^{a'}, χ^{b'}` (the transpose of `eqn:isoCocharLattices`). -/
theorem characterPair_eq_coverCharacterPair (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P =
      coverCharacterPair (quotientRestrictionScalarsEquiv ℚ_[3] P) :=
  characterPair_eq ℚ_[3] _ P

/-- The right square: the isomorphism of `eqn:isoCocharLattices` (`ω ↦ v₁`, `γω ↦ v₂`)
sends the element of `N_E` with coordinates `k` in `(ω, γω)` to the element of `N_E'` with
coordinates `k` in `(v₁, v₂)`. -/
theorem iso_quotientCochar (f : quotientLattice ≃ₗ[ℤ] coverLattice)
    (hω : ∀ x : quotientLattice, (x : ℚ × ℚ) = ω → (f x : ℚ × ℚ) = v₁)
    (hγω : ∀ x : quotientLattice, (x : ℚ × ℚ) = gamma ω → (f x : ℚ × ℚ) = v₂) (k : ℤ × ℤ) :
    f (quotientCochar k) = coverCochar k := by
  apply Subtype.ext
  rw [quotientCochar, map_add, map_zsmul, map_zsmul, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_smul, hω _ rfl, hγω _ rfl]
  rfl

/-- The diagram commutes. -/
theorem diagram_commutes (f : quotientLattice ≃ₗ[ℤ] coverLattice)
    (hω : ∀ x : quotientLattice, (x : ℚ × ℚ) = ω → (f x : ℚ × ℚ) = v₁)
    (hγω : ∀ x : quotientLattice, (x : ℚ × ℚ) = gamma ω → (f x : ℚ × ℚ) = v₂)
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    f (lowerLog P) = upperLog (quotientRestrictionScalarsEquiv ℚ_[3] P) := by
  rw [lowerLog, iso_quotientCochar f hω hγω, characterPair_eq_coverCharacterPair]
  rfl

/-- `𝒢₁(ℚ₃) = Hom_{Γ(w/v)}(M_E', E_w^×)`: every equivariant pair is the pair of
`x ∈ (E ⊗ ℚ₃)^×`. -/
theorem coverCharacterPair_surjective (q : RamifiedLocalModel.Points × RamifiedLocalModel.Points)
    (hq : IsEquivariantPair ramifiedτ .whole q) : ∃ x, coverCharacterPair x = q := by
  rw [isEquivariantPair_whole_iff ramifiedτ_involutive] at hq
  refine ⟨Units.map RamifiedQuotientLogarithm.place.symm.toMonoidHom q.1, Prod.ext ?_ ?_⟩
  · apply Units.ext
    simp [coverCharacterPair]
  · rw [hq]
    simp only [coverCharacterPair]
    rw [RamifiedQuotientLogarithm.mapped_conjugate]
    apply Units.ext
    simp [ramifiedτ]

/-- Surjectivity of the upper `ℓ_w` onto `(N_E')^{Γ(w/v)}`: `upper_surjective` (Shapiro's
lemma for the coinduced module `Hom(M_E', O_w^×)`) and the Hom description of `𝒢₁(ℚ₃)`. -/
theorem upperLog_surjective (m : coverLattice) (hm : gamma (m : ℚ × ℚ) = m) :
    ∃ x, upperLog x = m := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp m.2
  have hinv : IsInvariantPair .whole (a, b) := by
    have h1 := congrArg Prod.fst hm
    rw [← hab] at h1
    simp [gamma, v₁, v₂] at h1
    change (b, a) = (a, b)
    rw [h1]
  obtain ⟨q, hq, hqv⟩ := upper_surjective ramifiedτ ramifiedτ_involutive
    RamifiedLocalModel.integerValuation ramified_ord_τ RamifiedLocalModel.ramifiedParameter
    integerValuation_ramifiedParameter (a, b) hinv
  obtain ⟨x, rfl⟩ := coverCharacterPair_surjective q hq
  exact ⟨x, Subtype.ext (by rw [upperLog, hqv, ← hab]; rfl)⟩

/-- The image at the ramified place, by the paper's diagram: an invariant `n ∈ N_E^Γ` goes
to an invariant of `N_E'` under the `Γ`-isomorphism of `eqn:isoCocharLattices`, which is
hit by the upper `ℓ_w`; commutativity of the diagram and bijectivity of the vertical arrows
give a preimage under the lower `ℓ_w`. -/
theorem ramified_diagram (n : ℤ × ℤ) (hn : IsInvariantPair .whole n) :
    ∃ P, valuationPair RamifiedLocalModel.integerValuation
      (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom P) = n := by
  obtain ⟨f, hω, hγω, hγ⟩ := IsoCocharLattices.«eqn:isoCocharLattices».iso
  -- `n` is `Γ`-invariant, hence so is its image in `N_E'` (equivariance of the isomorphism).
  have hfix : (quotientCochar n : ℚ × ℚ) = gamma (quotientCochar n : ℚ × ℚ) := by
    change n.swap = n at hn
    have h : n.2 = n.1 := congrArg Prod.fst hn
    rw [coe_quotientCochar, map_add, map_zsmul, map_zsmul, h]
    change _ = n.1 • gamma ω + n.1 • (ω.swap.swap)
    rw [Prod.swap_swap, add_comm]
  obtain ⟨x, hx⟩ := upperLog_surjective (f (quotientCochar n)) (hγ _ _ hfix).symm
  refine ⟨(quotientRestrictionScalarsEquiv ℚ_[3]).symm x, quotientCochar_injective (f.injective ?_)⟩
  change f (lowerLog _) = _
  rw [diagram_commutes f hω hγω, Equiv.apply_symm_apply, hx]

end Diagram

/-- The image at the ramified place: `ramified_diagram`, read in `Hom_{Γ(w/v)}(M_E, E_w^×)`. -/
theorem ramified_image (n : ℤ × ℤ) (hn : IsInvariantPair .whole n) :
    ∃ q, IsEquivariantPair ramifiedτ .whole q ∧
      valuationPair RamifiedLocalModel.integerValuation q = n := by
  obtain ⟨P, hP⟩ := ramified_diagram n hn
  exact ⟨_, ramified_equivariant P, hP⟩

theorem ramified : FiniteFacts ramifiedLog .whole :=
  finiteFacts_of_hom .whole ramifiedτ RamifiedLocalModel.integerValuation ramified_ord_τ
    (characterPair ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom) ramifiedLog
    (fun P => by rw [ramifiedLog, localCocharacter, basisValuations_eq_valuationPair])
    (characterPair_mul ℚ_[3] _) ramified_equivariant ramified_pair_surjective
    QuotientLocalHaar.ramifiedCompactUnits ramified_mem_compactUnits_iff
    QuotientLocalHaar.isCompact_ramifiedCompactUnits
    QuotientLocalHaar.ramified_compact_subgroup_le ramified_image

theorem ramified_decomposition :
    (∀ a : ℚ_[3], RamifiedQuotientLogarithm.place ((1 : E) ⊗ₜ[ℚ] a) =
        algebraMap ℚ_[3] CyclotomicRamifiedField.Extension a) ∧
      (∀ y, ‖CyclotomicRamifiedField.conjugation y‖ = ‖y‖) ∧
      ∀ x : E ⊗[ℚ] ℚ_[3], RamifiedQuotientLogarithm.place (baseChangeConjugation ℚ_[3] x) =
        CyclotomicRamifiedField.conjugation (RamifiedQuotientLogarithm.place x) :=
  ⟨RamifiedQuotientLogarithm.place_scalar, CyclotomicRamifiedField.norm_conjugation,
    RamifiedQuotientLogarithm.place_conjugation⟩

end Ramified

/-! ### The complex place -/

section Archimedean

open ArchimedeanQuotientLogarithm CyclotomicArchimedean

/-- Complex conjugation on `ℂ^×`. -/
def complexτ : ℂˣ ≃* ℂˣ := Units.mapEquiv Complex.conjAe.toMulEquiv

theorem complexτ_involutive (z : ℂˣ) : complexτ (complexτ z) = z := by
  apply Units.ext
  simp [complexτ]

theorem order_τ (z : ℂˣ) : order (complexτ z) = order z := order_conjugate z

theorem archimedean_characterPair (P : Points) :
    characterPair ℝ place.toRingHom P = (pointEquiv P, complexτ (pointEquiv P)) := by
  rw [characterPair_eq]
  exact Prod.ext rfl (mapped_conjugate _)

theorem coordinate_pow (P : Points) (n : ℕ) : coordinate (P ^ n) = n * coordinate P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, coordinate_mul, ih]; push_cast; ring

/-- A compact subgroup of `T(ℝ)` has radial coordinate zero: `ℝ` has no
nontrivial compact subgroup. -/
theorem coordinate_eq_zero_of_compact (L : Subgroup Points) (hL : IsCompact (L : Set Points))
    (P : Points) (hP : P ∈ L) : coordinate P = 0 := by
  obtain ⟨M, hM⟩ := (hL.image continuous_coordinate).isBounded.exists_norm_le
  by_contra hc
  have hpos : 0 < |coordinate P| := abs_pos.mpr hc
  obtain ⟨n, hn⟩ := exists_nat_gt (M / |coordinate P|)
  have hbound := hM _ ⟨P ^ n, L.pow_mem hP n, rfl⟩
  rw [coordinate_pow, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hbound
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- `ℓ_w` is `ord_w ∘ ·` on `Hom(M_E, ℂ^×)`, converted to ray coordinates. -/
theorem archimedeanLog_eq (P : Points) :
    archimedeanLog P =
      let b := valuationPair order (characterPair ℝ place.toRingHom P)
      ((2 * b.1 + b.2) / 3, (b.1 + 2 * b.2) / 3) := rfl

/-- The section `t ↦ e^{-t}` of `ord_w = -log|·|`, fixed by complex conjugation. -/
def radialUnitSection : Multiplicative ℝ →* ℂˣ where
  toFun t := Units.mk0 (Real.exp (-t.toAdd) : ℂ) (by exact_mod_cast Real.exp_ne_zero _)
  map_one' := by ext; simp
  map_mul' s t := by
    ext
    simp only [toAdd_mul, neg_add, Real.exp_add, Units.val_mk0, Units.val_mul]
    push_cast
    rfl

theorem archimedean : ExactSequence archimedeanLog .whole ∧
    Set.range archimedeanLog = (invariantSpace .whole : Set (ℝ × ℝ)) := by
  have hequiv : ∀ P, IsEquivariantPair complexτ .whole (characterPair ℝ place.toRingHom P) :=
    fun P => by
      rw [isEquivariantPair_whole_iff complexτ_involutive, archimedean_characterPair]
  have hconv : ∀ b : ℝ × ℝ, IsInvariantPair .whole b →
      (((2 * b.1 + b.2) / 3, (b.1 + 2 * b.2) / 3) : ℝ × ℝ) = b := by
    intro b hb
    change b.swap = b at hb
    have h : b.2 = b.1 := congrArg Prod.fst hb
    ext <;> simp only [h] <;> ring
  have hlog : ∀ P, archimedeanLog P = valuationPair order (characterPair ℝ place.toRingHom P) :=
    fun P => by rw [archimedeanLog_eq]; exact hconv _ (draxl_mapsTo order order_τ .whole _ (hequiv P))
  -- The kernel is `Hom_Γ(M_E, {|z| = 1})`, i.e. radial coordinate zero.
  have hzero : ∀ P, archimedeanLog P = 0 ↔ coordinate P = 0 := fun P => by
    rw [hlog, draxl_ker, archimedean_characterPair, MonoidHom.mem_ker, MonoidHom.mem_ker,
      order_τ, and_self]
    change Multiplicative.ofAdd (-Real.log ‖((pointEquiv P : ℂˣ) : ℂ)‖) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, neg_eq_zero]
    rfl
  refine ⟨⟨fun P Q => ?_, fun P => ?_, ?_, ?_⟩, ?_⟩
  · rw [hlog, hlog, hlog, characterPair_mul, valuationPair_mul]
  · rw [hlog]
    exact draxl_mapsTo order order_τ .whole _ (hequiv P)
  · have hset : {P | archimedeanLog P = 0} = coordinate ⁻¹' Set.Icc 0 0 := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.Icc_self, Set.mem_singleton_iff]
      exact hzero P
    rw [hset]
    exact Cubic.PoissonSummation.ArchimedeanHaar.isCompact_coordinate_band 0 0
  · intro L hL P hP
    exact (hzero P).mpr (coordinate_eq_zero_of_compact L hL P hP)
  · ext x
    constructor
    · rintro ⟨P, rfl⟩
      rw [hlog]
      exact draxl_mapsTo order order_τ .whole _ (hequiv P)
    · intro hx
      obtain ⟨hq, hqx⟩ := draxl_section (τ := complexτ) order radialUnitSection
        (fun t => by
          apply Units.ext
          simp only [complexτ, radialUnitSection]
          simp
          rw [← Complex.exp_conj, map_neg, Complex.conj_ofReal])
        (fun t => by
          change Multiplicative.ofAdd (-Real.log ‖((Real.exp (-t.toAdd) : ℝ) : ℂ)‖) = t
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp,
            neg_neg]
          rfl)
        .whole x hx
      rw [isEquivariantPair_whole_iff complexτ_involutive] at hq
      refine ⟨pointEquiv.symm (radialUnitSection (Multiplicative.ofAdd x.1)), ?_⟩
      rw [hlog, archimedean_characterPair, ContinuousMulEquiv.apply_symm_apply, ← hq]
      exact hqx

theorem archimedean_decomposition :
    (∀ a : ℝ, CyclotomicArchimedean.place ((1 : E) ⊗ₜ[ℚ] a) = (a : ℂ)) ∧
      ∀ x : E ⊗[ℚ] ℝ, CyclotomicArchimedean.place (baseChangeConjugation ℝ x) =
        star (CyclotomicArchimedean.place x) :=
  ⟨CyclotomicArchimedean.place_scalar, CyclotomicArchimedean.place_conjugation⟩

end Archimedean

/-- Every rational prime falls under exactly one of the three finite cases. -/
theorem prime_cases (p : ℕ) (hp : p.Prime) : p = 3 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · left
    have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem «prop:basicfacts» : Claim where
  archimedean := archimedean
  split p _ _ := ⟨split_first p, split_second p⟩
  inert p _ _ := inert p
  ramified := ramified
  archimedean_decomposition := archimedean_decomposition
  split_decomposition p _ _ := split_decomposition p
  inert_decomposition p _ _ := inert_decomposition p
  ramified_decomposition := ramified_decomposition

end Cubic.ToricHeights.BasicFacts
