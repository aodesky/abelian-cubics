import Cubic.BoxHeight.CyclicCubicCharacters
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The cyclic cubic fields `K_a ⊂ ℚ(ζ_N)`

Supporting construction for `thm:lower` of `box_height_research_note.tex`. With the notation of
`CyclicCubicCharacters`, let `L = ℚ(ζ_N)` and identify `Gal(L/ℚ)` with `(ℤ/N)ˣ`. For
`a ≠ 0`, the fixed field `K_a` of `ker φ_a` is a cubic field, Galois over `ℚ`, totally real
(a complex place would have a stabilizer of order `2` in a group of order `3`), and
`K_a = K_b` only for `b = ±a`. An automorphism fixing `ζ_N^{N/c_a}` acts by some
`u ≡ 1 (mod c_a)`, so `K_a ⊂ M_a = ℚ(ζ_{c_a})`.
-/

noncomputable section

namespace Cubic.BoxHeight.CyclicCubicFields

open NumberField Polynomial Cubic.BoxHeight.CyclicCubicCharacters

variable (P : SplitSet)

/-- `ℚ(ζ_N)`. -/
abbrev L := CyclotomicField (N P) ℚ

instance isGalois_L : IsGalois ℚ (L P) := IsCyclotomicExtension.isGalois {N P} ℚ (L P)

/-- `Gal(ℚ(ζ_N)/ℚ) ≃ (ℤ/N)ˣ`. -/
def e : (L P ≃ₐ[ℚ] L P) ≃* (ZMod (N P))ˣ :=
  IsCyclotomicExtension.autEquivPow (L P) (cyclotomic.irreducible_rat (NeZero.pos _))

/-- The subgroup `ker φ_a` of the Galois group. -/
def V (a : ι P → ZMod 3) : Subgroup (L P ≃ₐ[ℚ] L P) := (φ P a).ker.comap (e P).toMonoidHom

instance normal_V (a : ι P → ZMod 3) : (V P a).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- `K_a`. -/
abbrev K (a : ι P → ZMod 3) : IntermediateField ℚ (L P) := IntermediateField.fixedField (V P a)

variable {P}

theorem index_V {a : ι P → ZMod 3} (ha : a ≠ 0) : (V P a).index = 3 := by
  have hc := Subgroup.index_comap_of_surjective (H := (φ P a).ker) (f := (e P).toMonoidHom)
    (e P).surjective
  rw [V, hc, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (φ_surjective P ha), Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

theorem finrank_K {a : ι P → ZMod 3} (ha : a ≠ 0) : Module.finrank ℚ (K P a) = 3 := by
  have h1 := Module.finrank_mul_finrank ℚ (K P a) (L P)
  rw [IntermediateField.finrank_fixedField_eq_card (V P a), ← IsGalois.card_aut_eq_finrank ℚ (L P),
    ← Subgroup.card_mul_index (V P a), index_V ha] at h1
  have hpos : 0 < Nat.card (V P a) := Nat.card_pos
  have : Module.finrank ℚ (K P a) * Nat.card (V P a) = 3 * Nat.card (V P a) := by linarith
  exact Nat.eq_of_mul_eq_mul_right hpos this

instance isGalois_K (a : ι P → ZMod 3) : IsGalois ℚ (K P a) := inferInstance

theorem card_gal_K {a : ι P → ZMod 3} (ha : a ≠ 0) : Nat.card (K P a ≃ₐ[ℚ] K P a) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_K ha]

open InfinitePlace in
theorem isTotallyReal_K {a : ι P → ZMod 3} (ha : a ≠ 0) : IsTotallyReal (K P a) := by
  constructor
  intro w
  by_contra hw
  have hram : w.IsRamified ℚ := by
    rw [isRamified_iff]
    exact ⟨not_isReal_iff_isComplex.mp hw, IsTotallyReal.isReal _⟩
  rw [isRamified_iff_card_stabilizer_eq_two] at hram
  have hdvd := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (K P a ≃ₐ[ℚ] K P a) w)
  rw [hram, card_gal_K ha] at hdvd
  omega

theorem rank_K {a : ι P → ZMod 3} (ha : a ≠ 0) : Units.rank (K P a) = 2 := by
  haveI := isTotallyReal_K ha
  rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, ← IsTotallyReal.finrank, finrank_K ha]

theorem ker_eq_of_V_eq {a b : ι P → ZMod 3} (h : V P a = V P b) : (φ P a).ker = (φ P b).ker := by
  ext u
  have := congrArg (fun H : Subgroup (L P ≃ₐ[ℚ] L P) => (e P).symm u ∈ H) h
  simpa [V] using this

/-- Distinct fields: `K_a = K_b` only for `b = ±a`. -/
theorem eq_or_eq_neg_of_K_eq {a b : ι P → ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : K P a = K P b) : b = a ∨ b = -a := by
  have h' : IntermediateField.fixedField (V P a) = IntermediateField.fixedField (V P b) := h
  have hV : V P a = V P b := by
    rw [← IntermediateField.fixingSubgroup_fixedField (V P a),
      ← IntermediateField.fixingSubgroup_fixedField (V P b), h']
  exact eq_or_eq_neg_of_ker_eq P ha hb (ker_eq_of_V_eq hV)

theorem K_neg (a : ι P → ZMod 3) : K P (-a) = K P a := by
  simp only [K, V, ker_neg]

/-- Isomorphic fields `K_a` coincide, since they are normal subfields of `L`. -/
theorem K_eq_of_algEquiv {a b : ι P → ZMod 3} (f : K P a ≃ₐ[ℚ] K P b) : K P a = K P b := by
  have h1 : ((K P b).val.comp f.toAlgHom).fieldRange = K P a :=
    AlgHom.fieldRange_of_normal _
  rw [← h1]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply, IntermediateField.coe_val]
  constructor
  · rintro ⟨y, rfl⟩; exact (f y).2
  · intro hx; exact ⟨f.symm ⟨x, hx⟩, by simp⟩

/-! ### The conductor field -/

variable (P)

/-- `ζ_N`. -/
abbrev ζ : L P := IsCyclotomicExtension.zeta (N P) ℚ (L P)

theorem hζ : IsPrimitiveRoot (ζ P) (N P) := IsCyclotomicExtension.zeta_spec (N P) ℚ (L P)

theorem N_eq (a : ι P → ZMod 3) : N P = N P / cond P a * cond P a :=
  (Nat.div_mul_cancel (cond_dvd_N P a)).symm

theorem primitive_cond (a : ι P → ZMod 3) :
    IsPrimitiveRoot (ζ P ^ (N P / cond P a)) (cond P a) :=
  (hζ P).pow (NeZero.pos _) (N_eq P a)

/-- `M_a = ℚ(ζ_{c_a}) ⊂ L`. -/
abbrev M (a : ι P → ZMod 3) : IntermediateField ℚ (L P) := IntermediateField.adjoin ℚ {ζ P ^ (N P / cond P a)}

instance (a : ι P → ZMod 3) : NeZero (cond P a) := ⟨(cond_pos P a).ne'⟩

instance isCyclotomic_M (a : ι P → ZMod 3) : IsCyclotomicExtension {cond P a} ℚ (M P a) :=
  (primitive_cond P a).intermediateField_adjoin_isCyclotomicExtension ℚ

variable {P}

/-- An automorphism fixing `ζ_N^{N/c}` acts by a unit `≡ 1 (mod c)`. -/
theorem cast_e_eq_one {a : ι P → ZMod 3} {σ : L P ≃ₐ[ℚ] L P}
    (hσ : σ (ζ P ^ (N P / cond P a)) = ζ P ^ (N P / cond P a)) :
    ZMod.castHom (cond_dvd_N P a) (ZMod (cond P a)) ((e P σ : (ZMod (N P))ˣ) : ZMod (N P)) = 1 := by
  set v := ((e P σ : (ZMod (N P))ˣ) : ZMod (N P)).val
  set d := N P / cond P a
  have hσζ : σ (ζ P) = ζ P ^ v := by
    have := ((hζ P).autToPow_spec ℚ σ).symm
    exact this
  have hv0 : v ≠ 0 := by
    intro h0
    have hz : ((e P σ : (ZMod (N P))ˣ) : ZMod (N P)) = 0 := (ZMod.val_eq_zero _).mp h0
    have hN1 : (1 : ℕ) < N P := by
      have : q P none ∣ N P := q_dvd_N P none
      have h9 : 9 ≤ N P := Nat.le_of_dvd (NeZero.pos _) this
      omega
    haveI : Nontrivial (ZMod (N P)) := ZMod.nontrivial_iff.mpr hN1.ne'
    exact (e P σ).ne_zero hz
  rw [map_pow, hσζ, ← pow_mul] at hσ
  have hζ0 : ζ P ^ d ≠ 0 := pow_ne_zero _ ((hζ P).ne_zero (NeZero.ne _))
  have h1 : ζ P ^ ((v - 1) * d) = 1 := by
    have : ζ P ^ ((v - 1) * d) * ζ P ^ d = 1 * ζ P ^ d := by
      rw [one_mul, ← pow_add, show (v - 1) * d + d = v * d by
        rw [← Nat.succ_pred_eq_of_ne_zero hv0]; simp [Nat.succ_mul]]
      exact hσ
    exact mul_right_cancel₀ hζ0 this
  have hdvd : N P ∣ (v - 1) * d := (hζ P).pow_eq_one_iff_dvd _ |>.mp h1
  rw [N_eq P a, mul_comm d] at hdvd
  have hc : cond P a ∣ v - 1 :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.div_pos (Nat.le_of_dvd (NeZero.pos _) (cond_dvd_N P a))
      (cond_pos P a)) hdvd
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have : ((v - 1 : ℕ) : ZMod (cond P a)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hc
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hv0), Nat.cast_one, sub_eq_zero] at this
  exact this

/-- `K_a ⊂ ℚ(ζ_{c_a})`. -/
theorem K_le_M (a : ι P → ZMod 3) : K P a ≤ M P a := by
  intro x hx
  rw [← IsGalois.fixedField_fixingSubgroup (M P a)]
  rintro ⟨σ, hσ⟩
  refine (IntermediateField.mem_fixedField_iff _ _).mp hx σ ?_
  have hfix : σ (ζ P ^ (N P / cond P a)) = ζ P ^ (N P / cond P a) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  change e P σ ∈ (φ P a).ker
  rw [MonoidHom.mem_ker]
  exact φ_eq_one_of_cast P (cast_e_eq_one hfix)

end Cubic.BoxHeight.CyclicCubicFields
