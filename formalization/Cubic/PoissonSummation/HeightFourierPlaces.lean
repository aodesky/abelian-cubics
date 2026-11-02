import Cubic.PoissonSummation.UnramifiedLocalFourier
import Cubic.PoissonSummation.LocalIntegrality

/-!
# The finite places of `prop:heightFourierTransform`

The generic place argument in `UnramifiedLocalFourier` needs three inputs. Here they are
supplied at the three kinds of place `w | v` with `v ≠ 3`:
the first split place, the second split place, and the inert place.

* The exact sequence and image of `ℓ_w` come from `prop:basicfacts` (`«prop:basicfacts»`).
  `K_v^max` is characterized there as the largest compact subgroup.
* The formula `H_v(x,-s) = q_v^{φ(ℓ_w x)}` holds at every point, not only on the cone.
  At a split prime, `v` has two places. Each contributes `q_v^{φ/2}`, and `φ` is invariant under
  the swap. At an inert prime, `q_w = q_v²` with global degree `2`.
* `1_v^{D₀}` is the cone indicator by `prop:localIntegrality` (`«prop:localIntegrality»`).

At `3`, the support, index and image statements come from `prop:localIntegrality`.
`ℓ_w` vanishes on `K_3^max` (`prop:basicfacts`), so the height is one on the support.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace Cubic.PoissonSummation.HeightFourierPlaces

open MeasureTheory
open Cubic.QuadraticCorrespondence Cubic.ToricHeights Cubic.OrbitParametrization
open CyclotomicTorusGalois QuotientLocalCharacters IntegralityStabilizer
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform
open UnramifiedLocalFourier
open CyclotomicRamifiedField (Extension integers)
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology QuotientLocalHaar

/-! ### From `prop:basicfacts` to the integral exact sequence -/

/-- `prop:basicfacts` for `ℓ_w = cocharacterEmbedding ∘ ℓ₀`, with `K` the maximal compact
subgroup, gives: `ℓ₀` is a homomorphism, its kernel is `K`, and its image is
`X_*(T_E)^{Γ(w/v)}`. -/
theorem integral_exact {G : Type} [Group G] [TopologicalSpace G] (ℓ₀ : G → ℤ × ℤ)
    (D : DecompositionGroup) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hmax : ∀ L : Subgroup G, IsCompact (L : Set G) → L ≤ K)
    (hF : FiniteFacts (fun x => cocharacterEmbedding (ℓ₀ x)) D) :
    (∀ x y, ℓ₀ (x * y) = ℓ₀ x + ℓ₀ y) ∧ (∀ x, ℓ₀ x = 0 ↔ x ∈ K) ∧
      Set.range ℓ₀ = (invariantLattice D : Set (ℤ × ℤ)) := by
  have hinj := BasicFacts.cocharacterEmbedding_injective
  have hmul : ∀ x y, ℓ₀ (x * y) = ℓ₀ x + ℓ₀ y := fun x y =>
    hinj (by rw [map_add]; exact hF.exact.map_mul x y)
  have hzero : ∀ x, cocharacterEmbedding (ℓ₀ x) = 0 ↔ ℓ₀ x = 0 := fun x => by
    rw [← map_zero cocharacterEmbedding, hinj.eq_iff]
  have hone : ℓ₀ 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    simpa using h
  refine ⟨hmul, fun x => ⟨fun hx => ?_, fun hx => (hzero x).mp
    (hF.exact.compact_subgroup_le_ker K hK x hx)⟩, ?_⟩
  · let L : Subgroup G :=
      { carrier := {x | ℓ₀ x = 0}
        one_mem' := hone
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [hmul, ha, hb, add_zero]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          have h := hmul a⁻¹ a
          rw [inv_mul_cancel, hone, ha, add_zero] at h
          exact h.symm }
    have hLc : IsCompact (L : Set G) := by
      have hset : (L : Set G) = {x | cocharacterEmbedding (ℓ₀ x) = 0} := by
        ext y
        exact (hzero y).symm
      rw [hset]
      exact hF.exact.isCompact_ker
    exact hmax L hLc hx
  · have h := hF.range_eq
    rw [Set.range_comp' cocharacterEmbedding ℓ₀] at h
    exact (Set.image_injective.mpr hinj) h

/-- An indicator with the stated level set is the `if` function. -/
theorem indicator_eq_ite {G : Type*} (S : Set G) (x : G) (P : Prop) [Decidable P]
    (h : S.indicator (1 : G → ℝ) x = 1 ↔ P) : S.indicator (1 : G → ℝ) x = if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP]; exact h.mpr hP
  · rw [if_neg hP]
    by_cases hx : x ∈ S
    · exact absurd (h.mp (by simp [hx])) hP
    · simp [hx]

attribute [local instance] Classical.propDecidable

/-! ### Split primes -/

section Split

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]

theorem one_lt_residueCard : 1 < residueCard p := by
  rw [residueCard, LocalLogarithmNormalization.padic_residue_cardinality]
  exact (Fact.out : p.Prime).one_lt

theorem residueCard_ne_zero : (residueCard p : ℂ) ≠ 0 := by
  have := one_lt_residueCard p
  exact_mod_cast (show residueCard p ≠ 0 by omega)

/-- The two splitting-field factors combine to `q_v^{φ(ℓ_w x)}` at the first place. -/
theorem splitInverseHeight_first (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    QuotientFiniteHeight.splitInverseHeight p s₀ σ x =
      (residueCard p : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding (splitCochar p x)) := by
  rw [QuotientFiniteHeight.splitInverseHeight, QuotientFiniteHeight.splitSecondCoordinates_eq,
    supportFunction_swap, ← Complex.cpow_add _ _ (residueCard_ne_zero p),
    CyclotomicField.finrank_eq_two]
  congr 1
  change supportFunction s₀ σ (cocharacterEmbedding (splitCochar p x)) / ((2 : ℕ) : ℂ) +
    supportFunction s₀ σ (cocharacterEmbedding (splitCochar p x)) / ((2 : ℕ) : ℂ) = _
  push_cast
  ring

/-- The same at the second place. -/
theorem splitInverseHeight_second (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    QuotientFiniteHeight.splitInverseHeight p s₀ σ x =
      (residueCard p : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding (splitSecondCochar p x)) := by
  rw [splitInverseHeight_first]
  congr 1
  change supportFunction s₀ σ (QuotientFiniteHeight.splitCoordinates p x) =
    supportFunction s₀ σ (QuotientFiniteHeight.splitSecondCoordinates p x)
  rw [QuotientFiniteHeight.splitSecondCoordinates_eq, supportFunction_swap]

theorem splitHyp_first : PlaceHyp (QuotientLocalHaar.splitMeasure p)
    (QuotientLocalHaar.splitCompactUnits p) .trivial (splitCochar p) (residueCard p)
    (QuotientFiniteHeight.splitInverseHeight p) (localIndicatorAt p) := by
  obtain ⟨hmul, hker, hrange⟩ := integral_exact (splitCochar p) .trivial _
    (QuotientLocalHaar.isCompact_splitCompactUnits p) (QuotientLocalHaar.split_compact_subgroup_le p)
    (BasicFacts.«prop:basicfacts».split p).1
  exact
    { isOpen := QuotientLocalHaar.isOpen_splitCompactUnits p
      measure_K := QuotientLocalHaar.splitMeasure_compactUnits p
      map_mul := hmul
      ker := hker
      range := hrange
      one_lt := one_lt_residueCard p
      height_eq := splitInverseHeight_first p
      indicator_eq := fun x => indicator_eq_ite _ x _
        (LocalIntegrality.«prop:localIntegrality».split_first p x) }

theorem splitHyp_second : PlaceHyp (QuotientLocalHaar.splitMeasure p)
    (QuotientLocalHaar.splitCompactUnits p) .trivial (splitSecondCochar p) (residueCard p)
    (QuotientFiniteHeight.splitInverseHeight p) (localIndicatorAt p) := by
  obtain ⟨hmul, hker, hrange⟩ := integral_exact (splitSecondCochar p) .trivial _
    (QuotientLocalHaar.isCompact_splitCompactUnits p) (QuotientLocalHaar.split_compact_subgroup_le p)
    (BasicFacts.«prop:basicfacts».split p).2
  exact
    { isOpen := QuotientLocalHaar.isOpen_splitCompactUnits p
      measure_K := QuotientLocalHaar.splitMeasure_compactUnits p
      map_mul := hmul
      ker := hker
      range := hrange
      one_lt := one_lt_residueCard p
      height_eq := splitInverseHeight_second p
      indicator_eq := fun x => indicator_eq_ite _ x _
        (LocalIntegrality.«prop:localIntegrality».split_second p x) }

end Split

/-! ### Inert primes -/

section Inert

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

/-- `q_w^{φ/[E:ℚ]} = (q_v²)^{φ/2} = q_v^{φ}`. -/
theorem inertInverseHeight_eq (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    QuotientFiniteHeight.inertInverseHeight p s₀ σ x =
      (residueCard p : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding (inertCochar p x)) := by
  rw [QuotientFiniteHeight.inertInverseHeight, CyclotomicInertField.card_residueField,
    CyclotomicField.finrank_eq_two, residueCard, LocalLogarithmNormalization.padic_residue_cardinality,
    Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
  congr 1
  change ((2 : ℕ) : ℂ) * (supportFunction s₀ σ (cocharacterEmbedding (inertCochar p x)) /
    ((2 : ℕ) : ℂ)) = _
  push_cast
  ring

theorem inertHyp : PlaceHyp (QuotientLocalHaar.inertMeasure p)
    (QuotientLocalHaar.inertCompactUnits p) .whole (inertCochar p) (residueCard p)
    (QuotientFiniteHeight.inertInverseHeight p) (localIndicatorAt p) := by
  obtain ⟨hmul, hker, hrange⟩ := integral_exact (inertCochar p) .whole _
    (QuotientLocalHaar.isCompact_inertCompactUnits p) (QuotientLocalHaar.inert_compact_subgroup_le p)
    (BasicFacts.«prop:basicfacts».inert p)
  have hq : 1 < residueCard p := by
    rw [residueCard, LocalLogarithmNormalization.padic_residue_cardinality]
    exact (Fact.out : p.Prime).one_lt
  exact
    { isOpen := QuotientLocalHaar.isOpen_inertCompactUnits p
      measure_K := QuotientLocalHaar.inertMeasure_compactUnits p
      map_mul := hmul
      ker := hker
      range := hrange
      one_lt := hq
      height_eq := inertInverseHeight_eq p
      indicator_eq := fun x => indicator_eq_ite _ x _
        (LocalIntegrality.«prop:localIntegrality».inert p x) }

end Inert

/-- `1_v^{D₀}` is `K_v^max`-invariant: `ℓ_w` vanishes on `K_v^max`. -/
theorem indicator_invariant {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} {K : Subgroup G} {D : DecompositionGroup}
    {ℓ : G → ℤ × ℤ} {q : ℕ} {h : ℂ → ℂ → G → ℂ} {ind : G → ℝ}
    (H : PlaceHyp μ K D ℓ q h ind) : ∀ k ∈ K, ∀ x, ind (x * k) = ind x := by
  intro k hk x
  rw [H.indicator_eq, H.indicator_eq, H.map_mul, (H.ker k).mpr hk, add_zero]

/-! ### The prime three -/

/-- `ℓ_w` vanishes on `K_3^max` (`prop:basicfacts`), so `H_3(x,-s) = 1` there. -/
theorem ramifiedInverseHeight_of_mem (s₀ σ : ℂ) {x : quotientFixedRing →ₐ[ℚ] ℚ_[3]}
    (hx : x ∈ QuotientLocalHaar.ramifiedCompactUnits) :
    QuotientFiniteHeight.ramifiedInverseHeight s₀ σ x = 1 := by
  have h0 : ramifiedLog x = 0 :=
    BasicFacts.«prop:basicfacts».ramified.exact.compact_subgroup_le_ker _
      QuotientLocalHaar.isCompact_ramifiedCompactUnits x hx
  have hc : QuotientFiniteHeight.ramifiedCoordinates x = 0 := h0
  rw [QuotientFiniteHeight.ramifiedInverseHeight, hc]
  simp [supportFunction]

theorem ramifiedInverseHeight_ne_zero (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    QuotientFiniteHeight.ramifiedInverseHeight s₀ σ x ≠ 0 := by
  rw [QuotientFiniteHeight.ramifiedInverseHeight, CyclotomicRamifiedField.card_residueField]
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem congruenceSet_subset :
    ramifiedCongruenceSet ⊆ (QuotientLocalHaar.ramifiedCompactUnits : Set _) := by
  intro x hx
  rw [← LocalIntegrality.ramifiedLevel_coe] at hx
  exact LocalIntegrality.ramifiedLevel_le hx

/-- `H_3(x,-s,D₀) = 1_{K_{3,2}}(x)` for every `s`. -/
theorem ramifiedIntegrand_eq (s₀ σ : ℂ) (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedIntegrand s₀ σ x = (localIndicatorAt 3 x : ℂ) := by
  unfold ramifiedIntegrand
  by_cases hx : x ∈ ramifiedCongruenceSet
  · rw [ramifiedInverseHeight_of_mem s₀ σ (congruenceSet_subset hx), one_mul]
  · have h0 : localIndicatorAt 3 x = 0 := by
      rw [← Function.notMem_support, LocalIntegrality.«prop:localIntegrality».support_three]
      exact hx
    rw [h0]
    simp

theorem three_support (s₀ σ : ℂ) :
    Function.support (ramifiedIntegrand s₀ σ) = ramifiedCongruenceSet := by
  rw [← LocalIntegrality.«prop:localIntegrality».support_three]
  ext x
  simp only [Function.mem_support, ramifiedIntegrand, ne_eq, mul_eq_zero, not_or,
    Complex.ofReal_eq_zero]
  exact ⟨fun h => h.2, fun h => ⟨ramifiedInverseHeight_ne_zero s₀ σ x, h⟩⟩

theorem three_index : ∃ H : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]),
    (H : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) = ramifiedCongruenceSet ∧
      H ≤ QuotientLocalHaar.ramifiedCompactUnits ∧
      H.relIndex QuotientLocalHaar.ramifiedCompactUnits = 6 := by
  refine ⟨AdelicLevel.ramifiedLevel, LocalIntegrality.ramifiedLevel_coe,
    LocalIntegrality.ramifiedLevel_le, ?_⟩
  let e := QuotientLocalModels.ramifiedEquiv.toMonoidHom
  have he : Function.Surjective e := QuotientLocalModels.ramifiedEquiv.surjective
  change (AdelicLevel.localLevelModel.comap e).relIndex
    (RamifiedLocalModel.compactUnits.comap e) = 6
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he,
    AdelicLevel.localLevelModel]
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _),
    RamifiedLocalModel.congruenceSubgroup_index]

theorem localPoint_surjective : Function.Surjective RamifiedQuotientLogarithm.localPoint := by
  intro u
  obtain ⟨x, hx⟩ := QuotientLocalModels.ramifiedEquiv.surjective u
  exact ⟨x, by rw [← QuotientLocalModels.ramifiedEquiv_apply, hx]⟩

theorem three_image : RamifiedQuotientLogarithm.localPoint '' ramifiedCongruenceSet =
    {u : Extensionˣ | ∃ a : integers, (u : Extension) = 1 + 3 * (a : Extension)} ∧
      ∀ u ∈ RamifiedQuotientLogarithm.localPoint '' ramifiedCongruenceSet,
        (u : Extension) ∈ integers ∧ ((u⁻¹ : Extensionˣ) : Extension) ∈ integers := by
  refine ⟨?_, ?_⟩
  · rw [LocalIntegrality.«prop:localIntegrality».congruence_three]
    exact Set.image_preimage_eq
      {u : Extensionˣ | ∃ a : integers, (u : Extension) = 1 + 3 * (a : Extension)}
      localPoint_surjective
  · rintro u ⟨x, hx, rfl⟩
    have hK := congruenceSet_subset hx
    change QuotientLocalModels.ramifiedEquiv x ∈ CyclotomicRamifiedField.compactUnits at hK
    rw [QuotientLocalModels.ramifiedEquiv_apply, CyclotomicRamifiedField.mem_compactUnits] at hK
    exact hK

theorem three_converges :
    ConvergesHolomorphically QuotientLocalHaar.ramifiedMeasure ramifiedIntegrand := by
  intro χ
  have hS : MeasurableSet ramifiedCongruenceSet := by
    rw [← LocalIntegrality.invariantLocus_three]
    exact QuotientLocalMeasure.measurableSet_invariantLocus 3
  have hf : ∀ s₀ σ : ℂ, (fun x => ramifiedIntegrand s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) =
      ramifiedCongruenceSet.indicator (fun x => ((χ x : Circle) : ℂ)⁻¹) := by
    intro s₀ σ
    funext x
    rw [ramifiedIntegrand_eq]
    by_cases hx : x ∈ ramifiedCongruenceSet
    · have h1 : localIndicatorAt 3 x = 1 := by
        rw [LocalIntegrality.localIndicatorAt_eq_one_iff, LocalIntegrality.invariantLocus_three]
        exact hx
      rw [h1, Set.indicator_of_mem hx]
      simp
    · have h0 : localIndicatorAt 3 x = 0 := by
        rw [← Function.notMem_support, LocalIntegrality.«prop:localIntegrality».support_three]
        exact hx
      rw [h0, Set.indicator_of_notMem hx]
      simp
  refine ⟨fun s₀ σ _ => ?_, ?_⟩
  · rw [hf s₀ σ, integrable_indicator_iff hS]
    exact ((continuous_character_inv χ).continuousOn.integrableOn_compact'
      QuotientLocalHaar.isCompact_ramifiedCompactUnits
      QuotientLocalHaar.isOpen_ramifiedCompactUnits.measurableSet).mono_set congruenceSet_subset
  · apply (differentiableOn_const
      (characterIntegral QuotientLocalHaar.ramifiedMeasure (ramifiedIntegrand 0 0) χ)).congr
    intro s _
    change (∫ x, ramifiedIntegrand s.1 s.2 x * ((χ x : Circle) : ℂ)⁻¹ ∂_) =
      ∫ x, ramifiedIntegrand 0 0 x * ((χ x : Circle) : ℂ)⁻¹ ∂_
    rw [hf s.1 s.2, hf 0 0]

end Cubic.PoissonSummation.HeightFourierPlaces
