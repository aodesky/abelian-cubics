import Cubic.BoxHeight.FieldPolynomials

/-!
# Counting the polynomials from one cyclic cubic field

For a cyclic cubic field `K` and `Y ≥ 0`, let `P_K(Y)` be the set of minimal polynomials of the
`α ∈ 𝒪_K ∖ ℤ` with `M(α) ≤ Y`. These are monic cyclic cubics of box height at most `3Y`, and
`#{α ∈ 𝒪_K : M(α) ≤ Y} ≤ (2 Y^{1/3} + 1) + 3 #P_K(Y)`: the rational integers `m` have
`M(m) = max(|m|, 1)³`, and at most the three Galois conjugates of `α` share its minimal
polynomial. Fields that are not isomorphic give disjoint sets.
-/

noncomputable section

namespace Cubic.BoxHeight.FieldCount

open NumberField Polynomial Cubic.BoxHeight.FieldPolynomials

variable {K : Type*} [Field K] [NumberField K]

theorem le_mahler (x : K) (φ : K →+* ℂ) : ‖φ x‖ ≤ mahler x := by
  classical
  have h1 : ∀ ψ : K →+* ℂ, (1 : ℝ) ≤ max ‖ψ x‖ 1 := fun _ => le_max_right _ _
  calc ‖φ x‖ ≤ max ‖φ x‖ 1 := le_max_left _ _
    _ = ∏ ψ : K →+* ℂ, if ψ = φ then max ‖ψ x‖ 1 else 1 := by
        rw [Finset.prod_ite_eq']; simp
    _ ≤ mahler x := by
        refine Finset.prod_le_prod (fun ψ _ => by split_ifs <;> positivity) fun ψ _ => ?_
        split_ifs; exacts [le_rfl, h1 ψ]

theorem one_le_mahler (x : K) : 1 ≤ mahler x := by
  have := Finset.prod_le_prod (s := (Finset.univ : Finset (K →+* ℂ))) (f := fun _ => (1 : ℝ))
    (g := fun φ => max ‖φ x‖ 1) (fun _ _ => zero_le_one) (fun _ _ => le_max_right _ _)
  simpa [mahler] using this

theorem finite_mahler (Y : ℝ) : {x : 𝓞 K | mahler (x : K) ≤ Y}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ Y
  refine (hfin.preimage (RingOfIntegers.coe_injective.injOn)).subset fun x hx => ?_
  exact ⟨x.2, fun φ => (le_mahler _ φ).trans hx⟩

/-- `P_K(Y)`. -/
def polySet (K : Type*) [Field K] [NumberField K] (Y : ℝ) : Set ℤ[X] :=
  {f | ∃ x : 𝓞 K, (x : K) ∉ (algebraMap ℚ K).range ∧ mahler (x : K) ≤ Y ∧ f = minpoly ℤ (x : K)}

theorem polySet_finite (Y : ℝ) : (polySet K Y).Finite := by
  refine ((finite_mahler (K := K) Y).image fun x : 𝓞 K => minpoly ℤ (x : K)).subset ?_
  rintro f ⟨x, -, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

variable (h3 : Module.finrank ℚ K = 3)
include h3

theorem polySet_subset_box [IsGalois ℚ K] (Y : ℝ) :
    polySet K Y ⊆ CubicTargets.BoxHeight.boxSet (3 * Y) := by
  rintro f ⟨x, hx, hY, rfl⟩
  have hb : ∀ i ≤ 2, |((minpoly ℤ (x : K)).coeff i : ℝ)| ≤ 3 * Y := fun i hi =>
    (coeff_bounds h3 hx i hi).trans (by linarith)
  refine ⟨⟨_, _, _, minpoly_int_eq_monicCubic h3 hx, hb 2 le_rfl, hb 1 (by norm_num),
    hb 0 (by norm_num)⟩, ?_⟩
  have hmap : (minpoly ℤ (x : K)).map (Int.castRingHom ℚ) = minpoly ℚ (x : K) :=
    minpoly_int_map x
  rw [hmap]
  exact cyclic_minpoly h3 hx

open scoped Classical in
/-- At most three elements share a minimal polynomial. -/
theorem card_fiber_le [IsGalois ℚ K] (s : Finset (𝓞 K)) (x : 𝓞 K) :
    (s.filter fun y : 𝓞 K => minpoly ℤ (y : K) = minpoly ℤ (x : K)).card ≤ 3 := by
  classical
  have hsub : (s.filter fun y : 𝓞 K => minpoly ℤ (y : K) = minpoly ℤ (x : K)).image
      (fun y : 𝓞 K => (y : K)) ⊆ (Finset.univ : Finset (K ≃ₐ[ℚ] K)).image (fun τ => τ (x : K)) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have he := (Finset.mem_filter.mp hy).2
    have hq : minpoly ℚ (y : K) = minpoly ℚ (x : K) := by
      rw [← minpoly_int_map, ← minpoly_int_map, he]
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := K)).mp hq
    exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, hτ⟩
  calc _ = ((s.filter fun y : 𝓞 K => minpoly ℤ (y : K) = minpoly ℤ (x : K)).image
        (fun y : 𝓞 K => (y : K))).card :=
        (Finset.card_image_of_injective _ RingOfIntegers.coe_injective).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (K ≃ₐ[ℚ] K)).card := Finset.card_image_le
    _ = 3 := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h3]

omit h3 in
/-- Integral elements of `K` lying in `ℚ` are rational integers. -/
theorem exists_int_of_mem_range {x : 𝓞 K} (hx : (x : K) ∈ (algebraMap ℚ K).range) :
    ∃ m : ℤ, (x : K) = m := by
  obtain ⟨q, hq⟩ := hx
  have hint : IsIntegral ℤ q := by
    have : IsIntegral ℤ (algebraMap ℚ K q) := by rw [hq]; exact RingOfIntegers.isIntegral_coe x
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨m, by rw [← hq, ← hm]; simp⟩

omit h3 in
theorem mahler_int (m : ℤ) : mahler ((m : ℤ) : K) = max |(m : ℝ)| 1 ^ Module.finrank ℚ K := by
  rw [mahler, ← NumberField.Embeddings.card K ℂ, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [map_intCast, Complex.norm_intCast]

/-- `#{α ∈ 𝒪_K : M(α) ≤ Y} ≤ 2 Y^{1/3} + 1 + 3 #P_K(Y)`. -/
theorem count_le [IsGalois ℚ K] (Y : ℝ) (hY : 0 ≤ Y) :
    (Nat.card {x : 𝓞 K // Height.mulHeight₁ (x : K) ≤ Y} : ℝ) ≤
      2 * Y ^ (1 / 3 : ℝ) + 1 + 3 * (Nat.card (polySet K Y) : ℝ) := by
  classical
  set S := (finite_mahler (K := K) Y).toFinset
  have hS : Nat.card {x : 𝓞 K // Height.mulHeight₁ (x : K) ≤ Y} = S.card := by
    have hset : {x : 𝓞 K | Height.mulHeight₁ (x : K) ≤ Y} = {x : 𝓞 K | mahler (x : K) ≤ Y} := by
      ext x; simp only [Set.mem_setOf_eq, mulHeight₁_eq_mahler]
    change Nat.card ↥{x : 𝓞 K | Height.mulHeight₁ (x : K) ≤ Y} = _
    rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (finite_mahler Y)]
  set Z := S.filter fun x : 𝓞 K => (x : K) ∈ (algebraMap ℚ K).range
  set R := S.filter fun x : 𝓞 K => (x : K) ∉ (algebraMap ℚ K).range
  have hsplit : S.card = Z.card + R.card := (Finset.card_filter_add_card_filter_not _).symm
  -- the non-rational elements
  set T := (polySet_finite (K := K) Y).toFinset
  have hR : R.card ≤ 3 * T.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := fun x : 𝓞 K => minpoly ℤ (x : K))
      (fun x hx => ?_) 3 (fun b _ => ?_)
    · rw [Finset.mem_filter] at hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hx.2, (finite_mahler Y).mem_toFinset.mp hx.1, rfl⟩
    · by_cases hb : ∃ a ∈ R, minpoly ℤ (a : K) = b
      · obtain ⟨a, -, rfl⟩ := hb
        exact card_fiber_le h3 R a
      · push_neg at hb
        rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a ha => hb a ha)]
        norm_num
  have hT : T.card = Nat.card (polySet K Y) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (polySet_finite Y)]
  -- the rational integers
  set B := ⌊Y ^ (1 / 3 : ℝ)⌋
  have hB0 : 0 ≤ Y ^ (1 / 3 : ℝ) := Real.rpow_nonneg hY _
  set g : 𝓞 K → ℤ := fun x => if h : (x : K) ∈ (algebraMap ℚ K).range then
    Classical.choose (exists_int_of_mem_range h) else 0
  have hg : ∀ x ∈ Z, (x : K) = (g x : K) := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    simp only [g, dif_pos h]
    exact Classical.choose_spec (exists_int_of_mem_range h)
  have hZ : Z.card ≤ (Finset.Icc (-B) B).card := by
    rw [← Finset.card_image_of_injOn (f := g) (fun x hx y hy hxy => RingOfIntegers.coe_injective
      (by show (x : K) = (y : K); rw [hg x hx, hg y hy, hxy]))]
    refine Finset.card_le_card fun m hm => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    have hmah : mahler (x : K) ≤ Y := (finite_mahler Y).mem_toFinset.mp (Finset.mem_filter.mp hx).1
    rw [hg x hx, mahler_int, h3] at hmah
    have habs : |(g x : ℝ)| ≤ Y ^ (1 / 3 : ℝ) := by
      have h1 : |(g x : ℝ)| ^ 3 ≤ Y :=
        (pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ 1) 3).trans hmah
      calc |(g x : ℝ)| = (|(g x : ℝ)| ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; norm_num
        _ ≤ Y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [abs_le] at habs
    rw [Finset.mem_Icc]
    constructor
    · have : -(g x) ≤ B := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr habs.2
  have hIcc : ((Finset.Icc (-B) B).card : ℝ) ≤ 2 * Y ^ (1 / 3 : ℝ) + 1 := by
    rw [Int.card_Icc]
    have hB := Int.floor_le (Y ^ (1 / 3 : ℝ))
    have hBn : 0 ≤ B := Int.floor_nonneg.mpr hB0
    have : ((B + 1 - -B).toNat : ℤ) = 2 * B + 1 := by rw [Int.toNat_of_nonneg (by omega)]; ring
    have h' : (((B + 1 - -B).toNat : ℕ) : ℝ) = 2 * (B : ℝ) + 1 := by exact_mod_cast this
    rw [h']; linarith
  rw [hS, hsplit]
  push_cast
  have hZ' : (Z.card : ℝ) ≤ (Finset.Icc (-B) B).card := by exact_mod_cast hZ
  have hR' : (R.card : ℝ) ≤ 3 * T.card := by exact_mod_cast hR
  rw [hT] at hR'
  linarith

omit h3 in
/-- A cubic field is generated by any of its irrational elements. -/
theorem adjoin_eq_top {K : Type*} [Field K] [NumberField K] (h3 : Module.finrank ℚ K = 3)
    {x : K} (hx : x ∉ (algebraMap ℚ K).range) : IntermediateField.adjoin ℚ {x} = ⊤ := by
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), natDegree_minpoly h3 hx,
    IntermediateField.finrank_top', h3]

omit h3 in
/-- Two cubic fields sharing one of these polynomials are isomorphic. -/
theorem algEquiv_of_mem {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (h₁ : Module.finrank ℚ K₁ = 3) (h₂ : Module.finrank ℚ K₂ = 3) {f : ℤ[X]} {Y₁ Y₂ : ℝ}
    (hf₁ : f ∈ polySet K₁ Y₁) (hf₂ : f ∈ polySet K₂ Y₂) : Nonempty (K₁ ≃ₐ[ℚ] K₂) := by
  obtain ⟨x₁, hx₁, -, rfl⟩ := hf₁
  obtain ⟨x₂, hx₂, -, he⟩ := hf₂
  have hq : minpoly ℚ (x₂ : K₂) = minpoly ℚ (x₁ : K₁) := by
    rw [← minpoly_int_map, ← minpoly_int_map, he]
  have e₁ := IntermediateField.adjoinRootEquivAdjoin ℚ (Algebra.IsIntegral.isIntegral (x₁ : K₁))
  have e₂ := IntermediateField.adjoinRootEquivAdjoin ℚ (Algebra.IsIntegral.isIntegral (x₂ : K₂))
  rw [hq] at e₂
  have t₁ := IntermediateField.equivOfEq (adjoin_eq_top h₁ hx₁)
  have t₂ := IntermediateField.equivOfEq (adjoin_eq_top h₂ hx₂)
  exact ⟨(IntermediateField.topEquiv.symm.trans t₁.symm).trans
    (e₁.symm.trans (e₂.trans (t₂.trans IntermediateField.topEquiv)))⟩

omit h3 in
/-- The box-height counts are finite. -/
theorem boxSet_finite (X : ℝ) : (CubicTargets.BoxHeight.boxSet X).Finite := by
  set B := ⌊X⌋
  refine ((((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).prod
    (Set.finite_Icc (-B) B)).image fun t : (ℤ × ℤ) × ℤ =>
      Cubic.Counting.GeneralMonicData.monicCubic t.1.1 t.1.2 t.2).subset ?_
  rintro f ⟨⟨a₂, a₁, a₀, rfl, h₂, h₁, h₀⟩, -⟩
  have hb : ∀ a : ℤ, (|a| : ℝ) ≤ X → a ∈ Set.Icc (-B) B := fun a ha => by
    rw [abs_le] at ha
    constructor
    · have : -a ≤ B := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr ha.2
  exact ⟨((a₂, a₁), a₀), ⟨⟨hb a₂ h₂, hb a₁ h₁⟩, hb a₀ h₀⟩, rfl⟩

end Cubic.BoxHeight.FieldCount
