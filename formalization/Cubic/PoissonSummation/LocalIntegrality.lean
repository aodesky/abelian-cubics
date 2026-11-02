import CubicTargets.PoissonSummation.LocalIntegrality
import Cubic.PoissonSummation.AdelicLevelInvariance
import Cubic.ToricHeights.BasicFacts
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# `prop:localIntegrality`

The proof follows the paper's proof step by step.

## Paper step → Lean

Part (1), `v ≠ 3`, uniformly for every place `w` over `v` (a place map
`E ⊗ ℚ_v → E_w` into an ultrametric normed field, with scalars embedded isometrically and a
valuation `ord_w` whose nonnegativity is the unit ball); `mem_invariantLocus_iff_inCone`.

* "`δ` is integral over `ℤ[e₂,e₃]`, so `1_v^{D₀}(x) = 1 ⇔ e₂(x), e₃(x) ∈ ℤ_v`":
  `QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus` (its proof is the monic
  quadratic `delta_quadratic` for `δ` over `ℤ_v[e₂,e₃]`, `lemma:affineIntegrality`'s argument).
  The paper's `e₃` is minus the constant coefficient `DescendedCoefficients.constantCoefficient`.
* "`r = χ^{v₁^∨+v₂^∨}(x)`, `s = χ^{3v₁^∨}(x)`, `t = χ^{3v₂^∨}(x)` in `E_w`": `rChar`, `sChar`,
  `tChar`, the quotient characters `QuotientLocalCharacters.localCharacter` with exponents
  `(1,1)`, `(2,1)`, `(1,2)` in the quotient basis, whose pullbacks to the `v^∨` basis are
  `v₁^∨+v₂^∨`, `3v₁^∨`, `3v₂^∨` (`pullback_r`, `pullback_s`, `pullback_t`).
* "the character formulas give `r = 1-3e₂`, `s+t = 2-9e₂+27e₃`": `character_formulas`, from the
  evaluation of the original coefficient functions in the characters
  (`QuotientCoefficientFormula.linearCoefficient_eq`, `constantCoefficient_eq`).
  "multiplicativity of characters gives `st = r³`": `s_mul_t` (`map_mul`, `map_pow`).
* "`s, t` are roots of the monic `U² - (s+t)U + r³ ∈ ℤ_v[U]`, hence `r, s, t ∈ O_{E,w}`", and the
  converse "`r³ = st`, `e₂ = (1-r)/3`, `e₃ = (s+t+1-3r)/27 ∈ O_{E,w} ∩ ℚ_v = ℤ_v`" (`v ≠ 3`):
  `coefficients_integral_iff`. Integral closedness of `O_{E,w}` for a monic quadratic is
  `norm_le_one_of_monic_quadratic`.
* "`ord_w(s) = 3⟨v₁^∨, ℓ_w(x)⟩`, `ord_w(t) = 3⟨v₂^∨, ℓ_w(x)⟩`": `norm_s_le_one_iff`,
  `norm_t_le_one_iff`, from the defining pairing `QuotientLocalCharacters.localCocharacter_pairing`.
* Instances: both split places (`split_first_locus`, `split_second_locus`) and the inert place
  (`inert_locus`); the Claim forms are `split_first`, `split_second`, `inert`.
* "`1_v^{D₀}` is `K_v^{max}`-invariant since `ℓ_w` is trivial on `K_v^{max}`
  (`prop:basicfacts`)": `split_cocharacter_compact`, `inert_cocharacter_compact` (from
  `Cubic.ToricHeights.BasicFacts.«prop:basicfacts»`: the kernel of `ℓ_w` contains every compact
  subgroup), then `split_mul_compact_iff`, `inert_mul_compact_iff` by additivity
  `localCocharacter_mul`; hence `stabilizer_away`. The same two facts and `0 ∈` cone give
  `K_v^{max} ⊆ {1_v^{D₀} = 1}` (`compact_le_integralLocus`), used in part (3).

Part (2), `v = 3`, `z = ι₃(P) = u + vζ`; `mem_invariantLocus_three_iff`.

* The local form of `eqn:integralityConditionsUsingCyclo`
  (`e₂,e₃,δ ∈ ℤ₃ ⇔ N ∈ 1+3ℤ₃ ∧ N(3-T) ∈ 1+27ℤ₃`): `hcond` inside
  `mem_invariantLocus_three_iff`, from the coefficient formulas
  `QuotientLocalIntegrality.ramified_coefficients` and
  `RamifiedLocalIntegrality.coefficientsIntegral_iff_conditions`. The proved rational statement
  `IntegralityConditions.«eqn:integralityConditionsUsingCyclo»` concerns rational points and
  `ℤ`; the paper's "in this local context take the form" is this `ℚ₃` analogue, proved from the
  same coefficient formulas.
* "`ord_𝔴(T-2) ≥ 2` and `ord_𝔴(1-T+N) ≥ 4`" and "the Newton polygon of
  `t²-Tt+N = (t-1)²-(T-2)(t-1)+1-T+N` gives `ord_𝔴(z-1) ≥ 2`": `newton_polygon`. The two
  congruences give `T-2 = 3α`, `1-T+N = 9β` with `α, β ∈ ℤ₃` (exact identities replacing the
  paper's computation of `N⁻¹` modulo `27`); the Newton polygon step is carried out by the
  rescaling `w = (z-1)/3` (`3` has `𝔴`-order `2`), a root of the monic `w²-αw+β ∈ ℤ₃[w]`, hence
  in `O_{E,w}` (`norm_le_one_of_monic_quadratic`).
* The converse "`z = 1+3x`, `x = c+dζ`: `N(z) ∈ 1+3ℤ₃`, `N(z)(3-Tr z) = 1+9(m-t²)-27mt`,
  `t²-m = 3c(c-d)`": `conditions_of_congruence`.
* `1+3O_{E,w} = 1+𝔴²`: `CyclotomicRamifiedField.maximalIdeal_sq` (`invariantLocus_three`).
* `K_{3,2}`: the project's subgroup `AdelicLevel.ramifiedLevel` is defined through the ramified
  local model; `ramifiedLevel_coe` unfolds it to `ι₃⁻¹(1+𝔴²)` by
  `RamifiedLocalIntegrality.mem_integralLocus_iff_maximalIdeal_sq`, and part (2) then gives
  `K_{3,2} = {1_3^{D₀} = 1}` (`ramifiedLevel_carrier_paper`).
* "`z ∈ O_{E,w}^×`, so the support lies in `K_3^{max}`": `ramifiedLevel_le`, from
  `‖1+3a‖ = 1` for `a ∈ O_{E,w}`.

Part (3): "`1_3^{D₀}` is the characteristic function of `K_{3,2}`, whose stabilizer in
`K_3^{max}` is `K_{3,2}`": `stabilizer_indicator_subgroup`, `stabilizer_three`. The product
stabilizer is the stabilizer of the product indicator (`product_eq_global`), tested on points
supported at a single place; this uses `1 ∈ {1_v^{D₀} = 1}` at every `v` (`one_mem_integralLocus`)
and the description of `1^{D₀}` as a finite product (`globalIndicator_eq`), both from parts (1)
and (2).

Remaining departures from the paper.
* The inputs `E_w`, `O_{E,w}` and `ord_w` are the project's concrete local models (see the
  target docstring), and `O_{E,w}` is the closed unit ball of an ultrametric norm, so "integral
  over `ℤ_v`" is used in the form of the monic-quadratic lemma rather than through a general
  integral-closure theorem.
* The local form of `eqn:integralityConditionsUsingCyclo` at three is proved from the local
  coefficient formulas (`RamifiedLocalIntegrality.coefficientsIntegral_iff_conditions`) rather
  than deduced from the rational statement, as described under part (2).
* The paper deduces `z ∈ O_{E,w}^×` directly from the two congruences, before the Newton
  polygon step; here it is read off afterwards from `z = 1+3a` (`ramifiedLevel_le`).
* In the Newton polygon step the paper's computation of `N⁻¹` modulo `27` is replaced by the
  exact identities `T-2 = 3α`, `1-T+N = 9β` and the rescaling `w = (z-1)/3`.
* Part (3)'s identification of the product stabilizer with the stabilizer of the product
  indicator is argued by testing at points supported at one place (`product_eq_global`); the
  paper takes this step as evident.
* The older coordinate/model computations of the local integral loci
  (`AdelicLevel.ramifiedLevel_carrier`, `AdelicHeightZetaData.local_compact_subset_integral` and
  the `Split/Inert/RamifiedLocalIntegrality` model characterizations) are not used; a transitive
  dependency probe confirms they are outside the dependency cone of `«prop:localIntegrality»`.
-/

noncomputable section

namespace Cubic.PoissonSummation.LocalIntegrality

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois IntegralityStabilizer FiniteEulerProduct QuotientFiniteFourierProduct
open CyclotomicRamifiedField (Extension integers)
open scoped TensorProduct RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Generalities on indicators and their stabilizers -/

theorem indicator_eq_iff {G : Type*} (S : Set G) (a b : G) :
    S.indicator (1 : G → ℝ) a = S.indicator 1 b ↔ (a ∈ S ↔ b ∈ S) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

theorem indicator_eq_one_iff {G : Type*} (S : Set G) (a : G) :
    S.indicator (1 : G → ℝ) a = 1 ↔ a ∈ S := by
  by_cases ha : a ∈ S <;> simp [ha]

/-- If translation by `K` preserves `S`, the stabilizer of its indicator in `K` is `K`. -/
theorem stabilizer_indicator_of_invariant {G : Type*} [Group G] (K : Subgroup G) (S : Set G)
    (hS : ∀ k ∈ K, ∀ x, x * k ∈ S ↔ x ∈ S) :
    translationStabilizer K (S.indicator (1 : G → ℝ)) = K := by
  ext k
  rw [mem_translationStabilizer]
  exact ⟨fun h => h.1, fun hk => ⟨hk, fun x => (indicator_eq_iff S _ _).2 (hS k hk x)⟩⟩

/-- The stabilizer in `K` of the indicator of a subgroup `H ≤ K` is `H` itself. -/
theorem stabilizer_indicator_subgroup {G : Type*} [Group G] (K H : Subgroup G) (hHK : H ≤ K) :
    translationStabilizer K ((H : Set G).indicator (1 : G → ℝ)) = H := by
  ext k
  rw [mem_translationStabilizer]
  constructor
  · rintro ⟨_, h⟩
    have h1 := h 1
    rw [one_mul, indicator_eq_iff] at h1
    exact h1.2 H.one_mem
  · intro hk
    exact ⟨hHK hk, fun x => (indicator_eq_iff _ _ _).2 (H.mul_mem_cancel_right hk)⟩

/-! ### Ultrametric generalities -/

/-- In an ultrametric normed field, a root of a monic quadratic whose coefficients lie in the
closed unit ball lies in the closed unit ball: the unit ball is integrally closed. -/
theorem norm_le_one_of_monic_quadratic {L : Type*} [NormedField L] [IsUltrametricDist L]
    {a b z : L} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hz : z ^ 2 - a * z + b = 0) : ‖z‖ ≤ 1 := by
  by_contra h
  have hz1 : 1 < ‖z‖ := lt_of_not_ge h
  have hmul : ‖a * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) ha
  have hsq : ‖z‖ ^ 2 ≤ max ‖a * z‖ ‖b‖ := by
    rw [← norm_pow, show z ^ 2 = a * z + -b by linear_combination hz]
    simpa only [norm_neg] using IsUltrametricDist.norm_add_le_max (a * z) (-b)
  have := hsq.trans (max_le hmul (hb.trans hz1.le))
  nlinarith

theorem norm_add_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] {a b : L}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem norm_mul_le_one {L : Type*} [NormedField L] {a b : L}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

theorem norm_one_add_of_norm_lt_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b : L}
    (hb : ‖b‖ < 1) : ‖1 + b‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hb.ne'), norm_one]
  exact max_eq_left hb.le

/-! ### Part (1): the characters `r, s, t` at a place over `v ≠ 3` -/

section Unramified

open QuotientLocalCharacters DescendedCoefficients CyclotomicRestrictionScalars
open Cubic.QuadraticCorrespondence.CyclotomicField (E)

variable (p : ℕ) [Fact p.Prime] {L : Type*} [NormedField L] [CharZero L]
  (place : E ⊗[ℚ] ℚ_[p] →+* L)

/-- The quotient exponents `(1,1)`, `(2,1)`, `(1,2)` are the characters `v₁^∨+v₂^∨`, `3v₁^∨`,
`3v₂^∨` in the `v^∨` basis (`CharacterLattice.pullback`). -/
theorem pullback_r : CharacterLattice.pullback (1, 1) = (1, 1) := rfl
theorem pullback_s : CharacterLattice.pullback (2, 1) = (3, 0) := rfl
theorem pullback_t : CharacterLattice.pullback (1, 2) = (0, 3) := rfl

/-- `r = χ^{v₁^∨+v₂^∨}(x)` in `E_w`. -/
def rChar (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : Lˣ :=
  localCharacter ℚ_[p] place P (Multiplicative.ofAdd (1, 1))
/-- `s = χ^{3v₁^∨}(x)` in `E_w`. -/
def sChar (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : Lˣ :=
  localCharacter ℚ_[p] place P (Multiplicative.ofAdd (2, 1))
/-- `t = χ^{3v₂^∨}(x)` in `E_w`. -/
def tChar (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : Lˣ :=
  localCharacter ℚ_[p] place P (Multiplicative.ofAdd (1, 2))

omit [CharZero L] in
theorem localCharacter_coe (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (m : ℤ × ℤ) :
    ((localCharacter ℚ_[p] place P (Multiplicative.ofAdd m) : Lˣ) : L) =
      ((Units.map place.toMonoidHom (quotientRestrictionScalarsEquiv ℚ_[p] P) ^ m.1 *
        Units.map place.toMonoidHom
          (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P)) ^ m.2 : Lˣ) : L) := by
  simp [localCharacter, characterValues_formula]

omit [CharZero L] in
/-- `st = r³`, by multiplicativity of characters. -/
theorem s_mul_t (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    sChar p place P * tChar p place P = rChar p place P ^ 3 := by
  simp only [sChar, tChar, rChar, ← map_mul, ← map_pow]
  rfl

omit [CharZero L] in
theorem r_coe (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((rChar p place P : Lˣ) : L) =
      place (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) *
        place (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) := by
  rw [rChar, localCharacter_coe]
  simp

omit [CharZero L] in
theorem s_coe (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((sChar p place P : Lˣ) : L) =
      place (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) ^ 2 *
        place (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) := by
  rw [sChar, localCharacter_coe]
  simp only [Units.val_mul, Units.coe_map, zpow_two, zpow_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  ring

omit [CharZero L] in
theorem t_coe (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((tChar p place P : Lˣ) : L) =
      place (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) *
        place (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) ^ 2 := by
  rw [tChar, localCharacter_coe]
  simp only [Units.val_mul, Units.coe_map, zpow_two, zpow_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  ring

omit [CharZero L] in
theorem s_add_t (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((sChar p place P : Lˣ) : L) + (tChar p place P : L) =
      place (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) *
        place (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) *
        (place (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) +
          place (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p])) := by
  rw [s_coe, t_coe]
  ring

/-- The character formulas: `r = 1 - 3e₂(x)` and `s + t = 2 - 9e₂(x) + 27e₃(x)`, where
`e₃ = -(constant coefficient)`. -/
theorem character_formulas (base : ℚ_[p] →+* L)
    (hbase : ∀ a : ℚ_[p], place ((1 : E) ⊗ₜ[ℚ] a) = base a) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((rChar p place P : Lˣ) : L) = 1 - 3 * base (P linearCoefficient) ∧
      ((sChar p place P : Lˣ) : L) + (tChar p place P : L) =
        2 - 9 * base (P linearCoefficient) + 27 * base (-P constantCoefficient) := by
  have h2 := QuotientCoefficientFormula.linearCoefficient_eq ℚ_[p] place P
  have h3 := QuotientCoefficientFormula.constantCoefficient_eq ℚ_[p] place P
  rw [hbase] at h2 h3
  rw [r_coe, s_add_t, h2, map_neg, h3]
  constructor <;> field_simp <;> ring

omit [CharZero L] in
theorem st_coe (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ((sChar p place P : Lˣ) : L) * (tChar p place P : L) = (rChar p place P : L) ^ 3 := by
  have h := congrArg Units.val (s_mul_t p place P)
  simpa using h

variable [IsUltrametricDist L]

/-- `e₂(x), e₃(x) ∈ ℤ_v ⇔ s, t ∈ O_{E,w}` for `v ≠ 3`. -/
theorem coefficients_integral_iff (hp : p ≠ 3) (base : ℚ_[p] →+* L)
    (hbase : ∀ a : ℚ_[p], place ((1 : E) ⊗ₜ[ℚ] a) = base a) (hnorm : ∀ a, ‖base a‖ = ‖a‖)
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    (‖P linearCoefficient‖ ≤ 1 ∧ ‖-P constantCoefficient‖ ≤ 1) ↔
      (‖((sChar p place P : Lˣ) : L)‖ ≤ 1 ∧ ‖((tChar p place P : Lˣ) : L)‖ ≤ 1) := by
  obtain ⟨hr, hst⟩ := character_formulas p place base hbase P
  have hmul := st_coe p place P
  set r : L := (rChar p place P : L)
  set s : L := (sChar p place P : L)
  set t : L := (tChar p place P : L)
  have hnat (n : ℕ) : ‖(n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L n
  constructor
  · rintro ⟨h2, h3⟩
    rw [← hnorm] at h2 h3
    -- `r, s + t ∈ ℤ_v`, hence `s, t` are roots of `U² - (s+t)U + r³ ∈ ℤ_v[U]`
    have hr1 : ‖r‖ ≤ 1 := by
      rw [hr, sub_eq_add_neg]
      exact norm_add_le_one (by simp) (by rw [norm_neg]; exact norm_mul_le_one (hnat 3) h2)
    have hsum : ‖s + t‖ ≤ 1 := by
      rw [hst, sub_eq_add_neg]
      exact norm_add_le_one (norm_add_le_one (hnat 2)
        (by rw [norm_neg]; exact norm_mul_le_one (hnat 9) h2)) (norm_mul_le_one (hnat 27) h3)
    have hprod : ‖r ^ 3‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg r) hr1
    exact ⟨norm_le_one_of_monic_quadratic hsum hprod (by rw [← hmul]; ring),
      norm_le_one_of_monic_quadratic hsum hprod (by rw [← hmul]; ring)⟩
  · rintro ⟨hs, ht⟩
    -- `r³ = st ∈ O_{E,w}`, so `r ∈ O_{E,w}`
    have hr1 : ‖r‖ ≤ 1 := by
      have h : ‖r‖ ^ 3 ≤ 1 := by
        rw [← norm_pow, ← hmul]
        exact norm_mul_le_one hs ht
      exact (pow_le_one_iff_of_nonneg (norm_nonneg r) (by norm_num)).mp h
    have h3 : ‖(3 : L)‖ = 1 := by
      rw [← map_ofNat base 3, hnorm]
      exact LocalCoefficientIntegrality.norm_three p hp
    have h27 : ‖(27 : L)‖ = 1 := by
      rw [← map_ofNat base 27, hnorm]
      exact LocalCoefficientIntegrality.norm_twentySeven p hp
    -- `e₂ = (1-r)/3`, `e₃ = (s+t+1-3r)/27`, and `O_{E,w} ∩ ℚ_v = ℤ_v`
    have he2 : base (P linearCoefficient) = (1 - r) / 3 := by
      rw [hr]
      field_simp
      ring
    have he3 : base (-P constantCoefficient) = (s + t + 1 - 3 * r) / 27 := by
      rw [hst, hr]
      field_simp
      ring
    have hle2 : ‖(1 - r) / 3‖ ≤ 1 := by
      rw [norm_div, h3, div_one, sub_eq_add_neg]
      exact norm_add_le_one (by simp) (by rw [norm_neg]; exact hr1)
    have hle3 : ‖(s + t + 1 - 3 * r) / 27‖ ≤ 1 := by
      rw [norm_div, h27, div_one, sub_eq_add_neg]
      exact norm_add_le_one (norm_add_le_one (norm_add_le_one hs ht) (by simp))
        (by rw [norm_neg]; exact norm_mul_le_one (hnat 3) hr1)
    rw [← hnorm, ← hnorm, he2, he3]
    exact ⟨hle2, hle3⟩

omit [CharZero L] [IsUltrametricDist L] in
/-- `ord_w(s) = 3⟨v₁^∨, ℓ_w(x)⟩`, so `s ∈ O_{E,w} ⇔ ⟨v₁^∨, ℓ_w(x)⟩ ≥ 0`. -/
theorem norm_s_le_one_iff (ord : Lˣ →* Multiplicative ℤ)
    (hord : ∀ u : Lˣ, ‖(u : L)‖ ≤ 1 ↔ 0 ≤ (ord u).toAdd) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ‖((sChar p place P : Lˣ) : L)‖ ≤ 1 ↔
      0 ≤ (Cubic.OrbitParametrization.CocharacterLattice.coordinates
        (localCocharacter ℚ_[p] place ord P)).1 := by
  have h := localCocharacter_pairing ℚ_[p] place ord P (2, 1)
  rw [pullback_s] at h
  simp only [Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero] at h
  rw [hord, sChar]
  constructor
  · intro h0
    have h1 : (0 : ℚ) ≤ ((ord (localCharacter ℚ_[p] place P (Multiplicative.ofAdd (2, 1)))).toAdd : ℚ) := by
      exact_mod_cast h0
    linarith
  · intro h0
    have h1 : (0 : ℚ) ≤ ((ord (localCharacter ℚ_[p] place P (Multiplicative.ofAdd (2, 1)))).toAdd : ℚ) := by
      linarith
    exact_mod_cast h1

omit [CharZero L] [IsUltrametricDist L] in
/-- `ord_w(t) = 3⟨v₂^∨, ℓ_w(x)⟩`. -/
theorem norm_t_le_one_iff (ord : Lˣ →* Multiplicative ℤ)
    (hord : ∀ u : Lˣ, ‖(u : L)‖ ≤ 1 ↔ 0 ≤ (ord u).toAdd) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ‖((tChar p place P : Lˣ) : L)‖ ≤ 1 ↔
      0 ≤ (Cubic.OrbitParametrization.CocharacterLattice.coordinates
        (localCocharacter ℚ_[p] place ord P)).2 := by
  have h := localCocharacter_pairing ℚ_[p] place ord P (1, 2)
  rw [pullback_t] at h
  simp only [Int.cast_ofNat, Int.cast_zero, zero_mul, zero_add] at h
  rw [hord, tChar]
  constructor
  · intro h0
    have h1 : (0 : ℚ) ≤ ((ord (localCharacter ℚ_[p] place P (Multiplicative.ofAdd (1, 2)))).toAdd : ℚ) := by
      exact_mod_cast h0
    linarith
  · intro h0
    have h1 : (0 : ℚ) ≤ ((ord (localCharacter ℚ_[p] place P (Multiplicative.ofAdd (1, 2)))).toAdd : ℚ) := by
      linarith
    exact_mod_cast h1

/-- Part (1), uniformly at a place `w` over `v ≠ 3`. -/
theorem mem_invariantLocus_iff_inCone (hp : p ≠ 3) (base : ℚ_[p] →+* L)
    (hbase : ∀ a : ℚ_[p], place ((1 : E) ⊗ₜ[ℚ] a) = base a) (hnorm : ∀ a, ‖base a‖ = ‖a‖)
    (ord : Lˣ →* Multiplicative ℤ) (hord : ∀ u : Lˣ, ‖(u : L)‖ ≤ 1 ↔ 0 ≤ (ord u).toAdd)
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ QuotientInvariantIntegrality.invariantLocus p ↔
      Cubic.PoissonSummation.LatticeCone.InCone (localCocharacter ℚ_[p] place ord P) := by
  -- `δ` is integral over `ℤ[e₂, e₃]`: the locus is `e₂, e₃ ∈ ℤ_v`
  rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus]
  change (‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1) ↔ _
  rw [← norm_neg (P constantCoefficient), coefficients_integral_iff p place hp base hbase hnorm,
    norm_s_le_one_iff p place ord hord, norm_t_le_one_iff p place ord hord]
  rfl

end Unramified

/-! ### Part (1) at the concrete places, and `K_v^{D₀} = K_v^{max}` -/

theorem padic_hord (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) :
    ‖(u : ℚ_[p])‖ ≤ 1 ↔ 0 ≤ (Cubic.OrbitParametrization.PadicMultiplicative.valuation p u).toAdd :=
  Padic.norm_le_one_iff_val_nonneg (u : ℚ_[p])

theorem inert_hord (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (u : InertLocalModel.Points p) :
    ‖(u : CyclotomicInertField.Extension p)‖ ≤ 1 ↔
      0 ≤ (InertLocalModel.integerValuation p u).toAdd := by
  change _ ↔ 0 ≤ InertLocalModel.ord p u
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [InertLocalModel.norm_eq_zpow_ord, zpow_le_one_iff_right₀ hp, neg_nonpos]

theorem split_first_locus (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    x ∈ QuotientInvariantIntegrality.invariantLocus p ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x) := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  refine mem_invariantLocus_iff_inCone p _ hp (RingHom.id _) (fun a => ?_) (fun a => rfl) _
    (padic_hord p) x
  change (SplitQuotientLogarithm.splitting p ((1 : CyclotomicField.E) ⊗ₜ[ℚ] a)).1 = a
  rw [SplitQuotientLogarithm.splitting_scalar]

theorem split_second_locus (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    x ∈ QuotientInvariantIntegrality.invariantLocus p ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x) := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  refine mem_invariantLocus_iff_inCone p _ hp (RingHom.id _) (fun a => ?_) (fun a => rfl) _
    (padic_hord p) x
  change (SplitQuotientLogarithm.splitting p ((1 : CyclotomicField.E) ⊗ₜ[ℚ] a)).2 = a
  rw [SplitQuotientLogarithm.splitting_scalar]

theorem inert_locus (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    x ∈ QuotientInvariantIntegrality.invariantLocus p ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
        (InertLocalModel.integerValuation p) x) := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 2); omega
  exact mem_invariantLocus_iff_inCone p _ hp (algebraMap ℚ_[p] (CyclotomicInertField.Extension p))
    (InertQuotientLogarithm.place_scalar p) (CyclotomicInertField.norm_algebraMap p) _
    (inert_hord p) x

/-- `N_E ↪ t_E` is injective, so `ℓ_w(k) = 0` in `t_E` means the lattice vector vanishes. -/
theorem eq_zero_of_cocharacterEmbedding_eq_zero {n : ℤ × ℤ}
    (h : CubicTargets.ToricHeights.BasicFacts.cocharacterEmbedding n = 0) : n = 0 := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [CubicTargets.ToricHeights.BasicFacts.cocharacterEmbedding, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Prod.fst_zero, Prod.snd_zero, Rat.cast_eq_zero] at h₁ h₂
  apply Cubic.OrbitParametrization.CocharacterLattice.coordinates_injective
  rw [map_zero]
  exact Prod.ext h₁ h₂

/-- `ℓ_w` is trivial on `K_v^{max}` at the first split place (`prop:basicfacts`). -/
theorem split_cocharacter_compact (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (k : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hk : k ∈ QuotientLocalHaar.splitCompactUnits p) :
    QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
      (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) k = 0 :=
  eq_zero_of_cocharacterEmbedding_eq_zero
    ((BasicFacts.«prop:basicfacts».split p).1.exact.compact_subgroup_le_ker
      (QuotientLocalHaar.splitCompactUnits p) (QuotientLocalHaar.isCompact_splitCompactUnits p) k hk)

/-- `ℓ_w` is trivial on `K_v^{max}` at the inert place (`prop:basicfacts`). -/
theorem inert_cocharacter_compact (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (k : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hk : k ∈ QuotientLocalHaar.inertCompactUnits p) :
    QuotientLocalCharacters.localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
      (InertLocalModel.integerValuation p) k = 0 :=
  eq_zero_of_cocharacterEmbedding_eq_zero
    ((BasicFacts.«prop:basicfacts».inert p).exact.compact_subgroup_le_ker
      (QuotientLocalHaar.inertCompactUnits p) (QuotientLocalHaar.isCompact_inertCompactUnits p) k hk)

/-- `ℓ_w` is trivial on `K_v^{max}` (`prop:basicfacts`), so by (1) the locus is `K_v^{max}`-stable. -/
theorem split_mul_compact_iff (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (x k : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hk : k ∈ QuotientLocalHaar.splitCompactUnits p) :
    x * k ∈ QuotientInvariantIntegrality.invariantLocus p ↔
      x ∈ QuotientInvariantIntegrality.invariantLocus p := by
  rw [split_first_locus, split_first_locus, QuotientLocalCharacters.localCocharacter_mul,
    split_cocharacter_compact p k hk, add_zero]

theorem inert_mul_compact_iff (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x k : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hk : k ∈ QuotientLocalHaar.inertCompactUnits p) :
    x * k ∈ QuotientInvariantIntegrality.invariantLocus p ↔
      x ∈ QuotientInvariantIntegrality.invariantLocus p := by
  rw [inert_locus, inert_locus, QuotientLocalCharacters.localCocharacter_mul,
    inert_cocharacter_compact p k hk, add_zero]

/-- `0` lies in the cone. -/
theorem inCone_zero : LatticeCone.InCone 0 := by
  simp [LatticeCone.InCone]

/-- `K_v^{max} ⊆ {1_v^{D₀} = 1}` for `v ≠ 3`: by (1), since `ℓ_w = 0` on `K_v^{max}`
(`prop:basicfacts`) and `0` lies in the cone. -/
theorem compact_le_integralLocus (p : Nat.Primes) (hp : p ≠ primeThree) :
    ∀ k : (family p).Carrier, k ∈ (family p).maxCompact → k ∈ (family p).integralLocus := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    intro k hk
    change k ∈ QuotientInvariantIntegrality.invariantLocus p
    rw [split_first_locus, split_cocharacter_compact p k hk]
    exact inCone_zero
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    intro k hk
    change k ∈ QuotientInvariantIntegrality.invariantLocus p
    rw [inert_locus, inert_cocharacter_compact p k hk]
    exact inCone_zero
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    exact (hp (Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)))).elim

theorem local_mul_compact_iff (p : Nat.Primes) (hp : p ≠ primeThree) :
    ∀ x k : (family p).Carrier, k ∈ (family p).maxCompact →
      (x * k ∈ (family p).integralLocus ↔ x ∈ (family p).integralLocus) := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact split_mul_compact_iff p
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inert_mul_compact_iff p
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    exact (hp (Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)))).elim

/-! ### Part (2): the Newton polygon at three -/

section Ramified

open RamifiedQuotientLogarithm CyclotomicCoefficients RamifiedLocalIntegrality
open CyclotomicRamifiedField (linear exists_linear norm_linear_le_one_iff linear_eq_zero_iff)

/-- `z = u + vζ` is a root of its characteristic polynomial `t² - Tt + N`. -/
theorem linear_charpoly (u v : ℚ_[3]) :
    linear u v ^ 2 - algebraMap ℚ_[3] Extension (traceForm u v) * linear u v +
      algebraMap ℚ_[3] Extension (normForm u v) = 0 := by
  simp only [linear, traceForm, normForm, map_sub, map_add, map_mul, map_pow, map_ofNat]
  linear_combination (algebraMap ℚ_[3] Extension v) ^ 2 * CyclotomicRamifiedField.zeta_relation

/-- Part (2), forward direction: the Newton polygon of `t² - Tt + N` in the variable `t - 1`.
From the two congruences, `ord_𝔴(T-2) ≥ 2` and `ord_𝔴(1-T+N) ≥ 4`, i.e. `T - 2 = 3α` and
`1 - T + N = 9β` with `α, β ∈ ℤ₃`; then `y = z - 1` is a root of `y² - 3αy + 9β`, so that
`w = y/3` is a root of the monic `w² - αw + β ∈ ℤ₃[w]` and `ord_𝔴(z - 1) ≥ 2`. -/
theorem newton_polygon (u v : ℚ_[3]) (h : Conditions u v) :
    ∃ a : integers, linear u v = 1 + 3 * (a : Extension) := by
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := h
  set N := normForm u v
  set T := traceForm u v
  have hn1 : ‖(n : ℚ_[3])‖ ≤ 1 := n.property
  have hm1 : ‖(m : ℚ_[3])‖ ≤ 1 := m.property
  have hthree : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := Padic.norm_p
  have hunit : ‖(1 + 3 * (n : ℚ_[3]))‖ = 1 := by
    apply norm_one_add_of_norm_lt_one
    rw [norm_mul, hthree]
    linarith
  have hne : (1 + 3 * (n : ℚ_[3])) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hunit
    exact zero_ne_one hunit
  -- `T - 2 = 3α` and `1 - T + N = 9β` with `α, β ∈ ℤ₃`
  set α : ℚ_[3] := ((n : ℚ_[3]) - 9 * m) / (1 + 3 * n)
  set β : ℚ_[3] := ((n : ℚ_[3]) ^ 2 + 3 * m) / (1 + 3 * n)
  have hα : T - 2 = 3 * α := by
    simp only [α]
    field_simp
    rw [hn] at hm
    linear_combination (-1 : ℚ_[3]) * hm
  have hβ : 1 - T + N = 9 * β := by
    have hT : T = 2 + 3 * α := by linear_combination hα
    simp only [β]
    rw [hT, hn]
    simp only [α]
    field_simp
    ring
  have hα1 : ‖α‖ ≤ 1 := by
    simp only [α]
    rw [norm_div, hunit, div_one, sub_eq_add_neg]
    exact norm_add_le_one hn1 (by
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℚ_[3] 9)
        (norm_nonneg _) hm1)
  have hβ1 : ‖β‖ ≤ 1 := by
    simp only [β]
    rw [norm_div, hunit, div_one]
    exact norm_add_le_one (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hn1)
      (norm_mul_le_one (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℚ_[3] 3) hm1)
  -- `w = (z - 1)/3` is a root of `w² - αw + β`
  set z := linear u v
  set w : Extension := (z - 1) / 3
  have hchar := linear_charpoly u v
  have hTe : algebraMap ℚ_[3] Extension T = 2 + 3 * algebraMap ℚ_[3] Extension α := by
    rw [show T = 2 + 3 * α by linear_combination hα, map_add, map_mul, map_ofNat, map_ofNat]
  have hNe : algebraMap ℚ_[3] Extension N =
      9 * algebraMap ℚ_[3] Extension β - 1 + algebraMap ℚ_[3] Extension T := by
    rw [show N = 9 * β - 1 + T by linear_combination hβ, map_add, map_sub, map_mul, map_ofNat,
      map_one]
  have hw : w ^ 2 - algebraMap ℚ_[3] Extension α * w + algebraMap ℚ_[3] Extension β = 0 := by
    rw [hNe, hTe] at hchar
    simp only [w]
    field_simp
    linear_combination hchar
  have hw1 : ‖w‖ ≤ 1 := norm_le_one_of_monic_quadratic
    (by rw [CyclotomicRamifiedField.norm_algebraMap]; exact hα1)
    (by rw [CyclotomicRamifiedField.norm_algebraMap]; exact hβ1) hw
  refine ⟨⟨w, hw1⟩, ?_⟩
  change z = 1 + 3 * ((z - 1) / 3)
  field_simp
  ring

theorem linear_injective {a b a' b' : ℚ_[3]} (h : linear a b = linear a' b') : a = a' ∧ b = b' := by
  have h0 : linear (a - a') (b - b') = 0 := by
    have : linear (a - a') (b - b') = linear a b - linear a' b' := by
      simp only [linear, map_sub]
      ring
    rw [this, h, sub_self]
  obtain ⟨h1, h2⟩ := (linear_eq_zero_iff _ _).1 h0
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- Part (2), converse: if `z = 1 + 3x` with `x = c + dζ ∈ O_{E,w}`, then with `t = Tr(x)`,
`m = N(x)`: `N(z) = 1 + 3t + 9m ∈ 1 + 3ℤ₃` and `N(z)(3 - Tr(z)) = 1 + 9(m - t²) - 27mt`, with
`t² - m = 3c(c - d)`, lies in `1 + 27ℤ₃`. -/
theorem conditions_of_congruence (u v : ℚ_[3]) (x : integers)
    (h : linear u v = 1 + 3 * (x : Extension)) : Conditions u v := by
  obtain ⟨c, d, hx⟩ := exists_linear (x : Extension)
  obtain ⟨hc, hd⟩ := (norm_linear_le_one_iff c d).1 (hx ▸ x.property)
  have hlin : linear u v = linear (1 + 3 * c) (3 * d) := by
    rw [h, hx]
    simp only [linear, map_add, map_mul, map_one, map_ofNat]
    ring
  obtain ⟨rfl, rfl⟩ := linear_injective hlin
  set c' : ℤ_[3] := ⟨c, hc⟩
  set d' : ℤ_[3] := ⟨d, hd⟩
  have hc' : ((c' : ℤ_[3]) : ℚ_[3]) = c := rfl
  have hd' : ((d' : ℤ_[3]) : ℚ_[3]) = d := rfl
  have h2 : (((2 : ℤ_[3])) : ℚ_[3]) = 2 := rfl
  have h3 : (((3 : ℤ_[3])) : ℚ_[3]) = 3 := rfl
  set t' : ℤ_[3] := 2 * c' - d'
  set m' : ℤ_[3] := c' ^ 2 + d' ^ 2 - c' * d'
  refine ⟨⟨t' + 3 * m', ?_⟩, ⟨-(c' * (c' - d') + m' * t'), ?_⟩⟩
  · simp only [t', m', normForm]
    push_cast
    simp only [hc', hd', h2, h3]
    ring
  · simp only [t', m', normForm, traceForm]
    push_cast
    simp only [hc', hd', h2]
    ring

/-- Part (2): `e₂(P), e₃(P), δ(P) ∈ ℤ₃ ⇔ ι₃(P) ∈ 1 + 3O_{E,w}`. -/
theorem mem_invariantLocus_three_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    P ∈ QuotientInvariantIntegrality.invariantLocus 3 ↔
      ∃ a : integers, ((localPoint P : Extensionˣ) : Extension) = 1 + 3 * (a : Extension) := by
  obtain ⟨u, v, hx⟩ := exists_linear ((localPoint P : Extensionˣ) : Extension)
  -- the local form of `eqn:integralityConditionsUsingCyclo`
  have hcond : P ∈ QuotientInvariantIntegrality.invariantLocus 3 ↔ Conditions u v := by
    rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus,
      ← coefficientsIntegral_iff_conditions]
    change (‖P DescendedCoefficients.linearCoefficient‖ ≤ 1 ∧
      ‖P DescendedCoefficients.constantCoefficient‖ ≤ 1) ↔ _
    rw [(QuotientLocalIntegrality.ramified_coefficients P u v hx).1,
      (QuotientLocalIntegrality.ramified_coefficients P u v hx).2]
    rfl
  rw [hcond, hx]
  exact ⟨newton_polygon u v, fun ⟨a, ha⟩ => conditions_of_congruence u v a ha⟩

end Ramified

/-! ### The Claim's parts (1) and (2) -/

theorem localIndicatorAt_eq_one_iff (p : ℕ) [Fact p.Prime] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localIndicatorAt p x = 1 ↔ x ∈ QuotientInvariantIntegrality.invariantLocus p :=
  indicator_eq_one_iff _ x

theorem split_first (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x) := by
  rw [localIndicatorAt_eq_one_iff, split_first_locus]

theorem split_second (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x) := by
  rw [localIndicatorAt_eq_one_iff, split_second_locus]

theorem inert (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localIndicatorAt p x = 1 ↔ LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
        (InertLocalModel.integerValuation p) x) := by
  rw [localIndicatorAt_eq_one_iff, inert_locus]

theorem stabilizer_away (p : Nat.Primes) (hp : p ≠ primeThree) :
    localStabilizer p = (family p).maxCompact :=
  stabilizer_indicator_of_invariant _ _ (fun k hk x => local_mul_compact_iff p hp x k hk)

theorem maximalIdeal_eq (a : integers) : a ∈ IsLocalRing.maximalIdeal integers ↔
    ∃ b : integers, (a : Extension) =
      (1 - RamifiedQuotientLogarithm.place (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[3]))) * b := by
  rw [CyclotomicRamifiedField.maximalIdeal_eq_parameter, Ideal.mem_span_singleton,
    RamifiedQuotientLogarithm.place_zeta, ← CyclotomicRamifiedField.coe_uniformizer]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

/-- `1 + 𝔴² = 1 + 3O_{E,w}`, since `𝔴² = 3O_{E,w}`. -/
theorem mem_ramifiedCongruenceSet_iff (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    x ∈ ramifiedCongruenceSet ↔
      ∃ a : integers, ((RamifiedQuotientLogarithm.localPoint x : Extensionˣ) : Extension) =
        1 + 3 * (a : Extension) := by
  rw [ramifiedCongruenceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [CyclotomicRamifiedField.maximalIdeal_sq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨b, by rw [h]; rfl⟩
  · rintro ⟨b, h⟩
    refine ⟨3 * b, ?_, by rw [h]; rfl⟩
    rw [CyclotomicRamifiedField.maximalIdeal_sq, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

theorem invariantLocus_three :
    QuotientInvariantIntegrality.invariantLocus 3 = ramifiedCongruenceSet := by
  ext x
  rw [mem_invariantLocus_three_iff, mem_ramifiedCongruenceSet_iff]

theorem support_three : Function.support (localIndicatorAt 3) = ramifiedCongruenceSet := by
  ext x
  rw [Function.mem_support, ← invariantLocus_three]
  by_cases hx : x ∈ QuotientInvariantIntegrality.invariantLocus 3 <;>
    simp [localIndicatorAt, hx]

theorem congruence_three : ramifiedCongruenceSet =
    {x | ∃ a : integers, ((RamifiedQuotientLogarithm.localPoint x : Extensionˣ) : Extension) =
      1 + 3 * (a : Extension)} := by
  ext x
  exact mem_ramifiedCongruenceSet_iff x

/-- The level at three, `K_{3,2}`, is `ι₃⁻¹(1+𝔴²)`: its definition through the ramified local
model is unfolded by `RamifiedLocalIntegrality.mem_integralLocus_iff_maximalIdeal_sq`. -/
theorem ramifiedLevel_coe :
    (AdelicLevel.ramifiedLevel : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) = ramifiedCongruenceSet := by
  ext x
  change QuotientLocalModels.ramifiedEquiv x ∈ RamifiedLocalModel.integralLocus ↔ _
  rw [RamifiedLocalIntegrality.mem_integralLocus_iff_maximalIdeal_sq,
    QuotientLocalModels.ramifiedEquiv_apply]
  rfl

/-- The paper-route carrier identity: `K_{3,2}` is the support `{1_3^{D₀} = 1}`, by part (2)
(`invariantLocus_three`, the Newton polygon argument). -/
theorem ramifiedLevel_carrier_paper :
    (AdelicLevel.ramifiedLevel : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) =
      QuotientInvariantIntegrality.invariantLocus 3 := by
  rw [ramifiedLevel_coe, invariantLocus_three]

/-- "These conditions imply `z ∈ O_{E,w}^×`, so the support of `1_3^{D₀}` is contained in
`K_3^{max}`": `‖1 + 3a‖ = 1` for `a ∈ O_{E,w}`. -/
theorem ramifiedLevel_le : AdelicLevel.ramifiedLevel ≤ QuotientLocalHaar.ramifiedCompactUnits := by
  intro x hx
  rw [← SetLike.mem_coe, ramifiedLevel_coe, mem_ramifiedCongruenceSet_iff] at hx
  obtain ⟨a, ha⟩ := hx
  change QuotientLocalModels.ramifiedEquiv x ∈ CyclotomicRamifiedField.compactUnits
  rw [QuotientLocalModels.ramifiedEquiv_apply, CyclotomicRamifiedField.mem_compactUnits_iff_norm_one]
  rw [ha]
  apply norm_one_add_of_norm_lt_one
  rw [norm_mul, CyclotomicRamifiedField.norm_three]
  have : ‖(a : Extension)‖ ≤ 1 := a.property
  nlinarith [norm_nonneg (a : Extension)]

/-! ### Part (3) -/

theorem stabilizer_three (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    x ∈ localStabilizer primeThree ↔ x ∈ ramifiedCongruenceSet := by
  change x ∈ translationStabilizer QuotientLocalHaar.ramifiedCompactUnits
    ((QuotientInvariantIntegrality.invariantLocus 3).indicator 1) ↔ _
  rw [← ramifiedLevel_carrier_paper,
    stabilizer_indicator_subgroup _ _ ramifiedLevel_le, ← SetLike.mem_coe, ramifiedLevel_coe]

theorem one_mem_integralLocus (p : Nat.Primes) : (1 : (family p).Carrier) ∈ (family p).integralLocus := by
  by_cases hp : p = primeThree
  · subst hp
    change (1 : quotientFixedRing →ₐ[ℚ] ℚ_[3]) ∈ QuotientInvariantIntegrality.invariantLocus 3
    rw [← ramifiedLevel_carrier_paper]
    exact AdelicLevel.ramifiedLevel.one_mem
  · exact compact_le_integralLocus p hp 1 (family p).maxCompact.one_mem

open Classical in
/-- `1^{D₀}` is the indicator of the adelic points that are locally integral at every prime. -/
theorem globalIndicator_eq (x : AdelicData.Points) :
    globalIndicator x = if ∀ p, x.2 p ∈ (family p).integralLocus then 1 else 0 := by
  have hfin : {p : Nat.Primes | ¬ x.2 p ∈ (family p).maxCompact}.Finite :=
    Filter.eventually_cofinite.mp x.2.eventually
  set F : Finset Nat.Primes := hfin.toFinset ∪ {primeThree}
  have hout : ∀ p ∉ F, x.2 p ∈ (family p).integralLocus := by
    intro p hp
    simp only [F, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Finset.mem_singleton, not_or, not_not] at hp
    exact compact_le_integralLocus p hp.2 _ hp.1
  rw [globalIndicator, archimedeanIndicator, one_mul]
  simp only [localIndicator]
  rw [tprod_eq_prod (s := F) (fun p hp => (indicator_eq_one_iff _ _).2 (hout p hp))]
  split_ifs with h
  · exact Finset.prod_eq_one (fun p _ => (indicator_eq_one_iff _ _).2 (h p))
  · push_neg at h
    obtain ⟨p, hp⟩ := h
    have hpF : p ∈ F := by
      by_contra hF
      exact hp (hout p hF)
    exact Finset.prod_eq_zero hpF (Set.indicator_of_notMem hp _)

theorem globalIndicator_eq_iff (x y : AdelicData.Points) :
    globalIndicator x = globalIndicator y ↔
      ((∀ p, x.2 p ∈ (family p).integralLocus) ↔ ∀ p, y.2 p ∈ (family p).integralLocus) := by
  rw [globalIndicator_eq, globalIndicator_eq]
  by_cases hx : ∀ p, x.2 p ∈ (family p).integralLocus <;>
    by_cases hy : ∀ p, y.2 p ∈ (family p).integralLocus
  · rw [if_pos hx, if_pos hy]
    exact iff_of_true rfl (iff_of_true hx hy)
  · rw [if_pos hx, if_neg hy]
    exact iff_of_false one_ne_zero (fun h => hy (h.1 hx))
  · rw [if_neg hx, if_pos hy]
    exact iff_of_false zero_ne_one (fun h => hx (h.2 hy))
  · rw [if_neg hx, if_neg hy]
    exact iff_of_true rfl (iff_of_false hx hy)

theorem product_eq_global : productStabilizer = globalStabilizer := by
  ext k
  constructor
  · rintro ⟨hkinf, hkp⟩
    refine ⟨⟨hkinf, fun p => (hkp p).1⟩, fun x => ?_⟩
    rw [globalIndicator_eq_iff]
    refine forall_congr' fun p => ?_
    exact (indicator_eq_iff _ _ _).1 ((hkp p).2 (x.2 p))
  · rintro ⟨hkK, hk⟩
    refine ⟨hkK.1, fun p => ⟨hkK.2 p, fun y => ?_⟩⟩
    -- Every local component of `k` is locally integral: test at the identity.
    have hall : ∀ q, k.2 q ∈ (family q).integralLocus := by
      have h1 := hk 1
      rw [one_mul, globalIndicator_eq_iff] at h1
      exact h1.2 (fun q => one_mem_integralLocus q)
    -- Test at the point supported at `p` with component `y`.
    let x : AdelicData.Points :=
      (1, RestrictedProduct.mulSingle (fun q => (family q).maxCompact) p y)
    have hx : ∀ q, q ≠ p → x.2 q = 1 := fun q hq =>
      RestrictedProduct.mulSingle_eq_of_ne (G := fun q => (family q).Carrier)
        (fun q => (family q).maxCompact) y hq
    have hxp : x.2 p = y := Pi.mulSingle_eq_same (M := fun q => (family q).Carrier) p y
    have h := hk x
    rw [globalIndicator_eq_iff] at h
    rw [localIndicator, indicator_eq_iff]
    constructor
    · intro hyk
      have := h.1 (fun q => by
        by_cases hq : q = p
        · subst hq
          change x.2 q * k.2 q ∈ _
          rw [hxp]
          exact hyk
        · change x.2 q * k.2 q ∈ _
          rw [hx q hq, one_mul]
          exact hall q)
      have hp := this p
      rwa [hxp] at hp
    · intro hy
      have := h.2 (fun q => by
        by_cases hq : q = p
        · subst hq
          rw [hxp]
          exact hy
        · rw [hx q hq]
          exact one_mem_integralLocus q)
      have hp := this p
      change x.2 p * k.2 p ∈ _ at hp
      rwa [hxp] at hp

theorem product_eq : (productStabilizer : Set AdelicData.Points) =
    {x | x.1 ∈ archimedeanMaxCompact ∧
      (x.2 primeThree : quotientFixedRing →ₐ[ℚ] ℚ_[3]) ∈ ramifiedCongruenceSet ∧
      ∀ p : Nat.Primes, p ≠ primeThree → x.2 p ∈ (family p).maxCompact} := by
  ext x
  change (x.1 ∈ archimedeanMaxCompact ∧ ∀ p, x.2 p ∈ localStabilizer p) ↔ _
  refine and_congr Iff.rfl ⟨fun h => ⟨(stabilizer_three _).1 (h primeThree), fun p hp => ?_⟩,
    fun h p => ?_⟩
  · rw [← stabilizer_away p hp]
    exact h p
  · by_cases hp : p = primeThree
    · subst hp
      exact (stabilizer_three _).2 h.1
    · rw [stabilizer_away p hp]
      exact h.2 p hp

theorem product_eq_level : productStabilizer = AdelicLevel.level := by
  apply SetLike.coe_injective
  rw [product_eq]
  ext x
  change _ ↔ x.1 ∈ ArchimedeanHaar.coordinateHom.ker ∧
    ((∀ p, x.2 p ∈ (family p).maxCompact) ∧
      (x.2 primeThree : quotientFixedRing →ₐ[ℚ] ℚ_[3]) ∈ AdelicLevel.ramifiedLevel)
  rw [← SetLike.mem_coe (x := (x.2 primeThree : quotientFixedRing →ₐ[ℚ] ℚ_[3])), ramifiedLevel_coe]
  refine and_congr Iff.rfl ⟨fun h => ⟨fun p => ?_, h.1⟩, fun h => ⟨h.2, fun p _ => h.1 p⟩⟩
  by_cases hp : p = primeThree
  · subst hp
    rw [← ramifiedLevel_coe] at h
    exact ramifiedLevel_le h.1
  · exact h.2 p hp

theorem product_le : productStabilizer ≤ AdelicCompactQuotient.maximalCompact := by
  rw [product_eq_level]
  exact AdelicLevel.level_le_maximalCompact

theorem «prop:localIntegrality» : CubicTargets.PoissonSummation.LocalIntegrality.Claim where
  split_first := split_first
  split_second := split_second
  inert := inert
  stabilizer_away := stabilizer_away
  maximalIdeal_eq := maximalIdeal_eq
  maximalIdeal_sq := CyclotomicRamifiedField.maximalIdeal_sq
  support_three := support_three
  congruence_three := congruence_three
  subgroup_three := ⟨AdelicLevel.ramifiedLevel, ramifiedLevel_coe, ramifiedLevel_le⟩
  product_le := product_le
  product_eq_global := product_eq_global
  stabilizer_three := stabilizer_three
  product_eq := product_eq
  product_eq_level := product_eq_level

end Cubic.PoissonSummation.LocalIntegrality
