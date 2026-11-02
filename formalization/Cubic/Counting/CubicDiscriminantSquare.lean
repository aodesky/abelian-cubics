import Cubic.QuadraticCorrespondence.SmallGaloisGroup
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Square discriminants of monic rational cubics

Supporting facts for `prop:traceZeroAsymptotic`. A monic cubic `f ∈ ℚ[t]` with Galois group
`C₃` or split over `ℚ` has square discriminant. Conversely, if the discriminant is a nonzero
square `d²`, then the product `δ` of the root differences is `±d`, so it is fixed by the
Galois group. A Galois element fixing one root and swapping the other two would send `δ` to
`-δ`; hence every nontrivial element moves every root. The Galois group then embeds in the
three roots by `σ ↦ σ(x)` and has no element of order two, so it is trivial (the cubic
splits) or cyclic of order three.
-/

noncomputable section

namespace Cubic.Counting.CubicDiscriminantSquare

open Polynomial Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.QuadraticCorrespondence.SmallGaloisGroup

variable {P : _root_.Cubic ℚ}

theorem a_ne_zero (ha : P.a = 1) : P.a ≠ 0 := by rw [ha]; exact one_ne_zero

theorem discr_square_of_splits (ha : P.a = 1) (h : P.toPoly.Splits) :
    ∃ d : ℚ, P.discr = d ^ 2 := by
  have hs : (P.toPoly.map (RingHom.id ℚ)).Splits := by rw [Polynomial.map_id]; exact h
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three (a_ne_zero ha)).mp hs
  refine ⟨(x - y) * (x - z) * (y - z), ?_⟩
  have := _root_.Cubic.discr_eq_prod_three_roots (a_ne_zero ha) h3
  simpa [ha, mul_assoc] using this

theorem discr_square_of_cyclic (ha : P.a = 1) (h : HasCyclicCubicGaloisGroup P.toPoly) :
    ∃ d : ℚ, P.discr = d ^ 2 := by
  by_cases h0 : P.discr = 0
  · exact ⟨0, by rw [h0]; ring⟩
  let L := P.toPoly.SplittingField
  have hsL : (P.toPoly.map (algebraMap ℚ L)).Splits := SplittingField.splits P.toPoly
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three (a_ne_zero ha)).mp hsL
  have hsep : P.toPoly.Separable := by
    have hnd := (_root_.Cubic.discr_ne_zero_iff_roots_nodup (a_ne_zero ha) hsL).mp h0
    rw [_root_.Cubic.roots, _root_.Cubic.map_toPoly] at hnd
    rwa [nodup_roots_iff_of_splits (map_ne_zero (_root_.Cubic.ne_zero_of_a_ne_zero
      (a_ne_zero ha))) hsL, separable_map] at hnd
  have hfin : Module.finrank ℚ L = 3 := by
    obtain ⟨e⟩ := h
    rw [← Polynomial.Gal.card_of_separable hsep, Nat.card_congr e.toEquiv]
    simp
  set δ : L := (x - y) * (x - z) * (y - z)
  have hδ : algebraMap ℚ L P.discr = δ ^ 2 := by
    have := _root_.Cubic.discr_eq_prod_three_roots (a_ne_zero ha) h3
    simpa [ha, δ, mul_assoc] using this
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  have hle : (minpoly ℚ δ).natDegree ≤ 2 := by
    have hp : aeval δ (X ^ 2 - C P.discr) = 0 := by simp [hδ]
    calc (minpoly ℚ δ).natDegree ≤ (X ^ 2 - C P.discr).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd ℚ δ hp) (X_pow_sub_C_ne_zero two_pos _)
      _ = 2 := natDegree_X_pow_sub_C
  have hdvd := minpoly.degree_dvd hint
  rw [hfin] at hdvd
  have hpos := minpoly.natDegree_pos hint
  have h1 : (minpoly ℚ δ).natDegree = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> omega
  obtain ⟨d, hd⟩ := minpoly.natDegree_eq_one_iff.mp h1
  refine ⟨d, (algebraMap ℚ L).injective ?_⟩
  rw [hδ, map_pow, hd]

/-- A Galois element that fixes one root, and fixes the product of the root differences
(which is nonzero), fixes every root. -/
theorem eq_one_of_fix {L : Type*} [Field L] [Algebra ℚ L] {p : ℚ[X]} (σ : L ≃ₐ[ℚ] L)
    {u v w : L} (hroot : ∀ r : L, aeval r p = 0 ↔ r = u ∨ r = v ∨ r = w)
    (hδ : σ ((u - v) * (u - w) * (v - w)) = (u - v) * (u - w) * (v - w))
    (hδ0 : (u - v) * (u - w) * (v - w) ≠ 0) (hu : σ u = u) :
    σ v = v ∧ σ w = w := by
  have huv : u ≠ v := fun h => hδ0 (by rw [h]; ring)
  have huw : u ≠ w := fun h => hδ0 (by rw [h]; ring)
  have hvw : v ≠ w := fun h => hδ0 (by rw [h]; ring)
  have hmap : ∀ r, aeval r p = 0 → aeval (σ r) p = 0 := fun r hr => by
    rw [aeval_algHom_apply σ, hr, map_zero]
  have hv := (hroot _).mp (hmap v ((hroot v).mpr (Or.inr (Or.inl rfl))))
  have hw := (hroot _).mp (hmap w ((hroot w).mpr (Or.inr (Or.inr rfl))))
  have hσv : σ v = v := by
    rcases hv with hv | hv | hv
    · exact absurd (σ.injective (hv.trans hu.symm)) (Ne.symm huv)
    · exact hv
    · exfalso
      have hσw : σ w = v := by
        rcases hw with hw | hw | hw
        · exact absurd (σ.injective (hw.trans hu.symm)) (Ne.symm huw)
        · exact hw
        · exact absurd (σ.injective (hw.trans hv.symm)) hvw.symm
      apply hδ0
      have h := hδ
      simp only [map_mul, map_sub, hu, hv, hσw] at h
      have h2 : (2 : L) * ((u - v) * (u - w) * (v - w)) = 0 := by linear_combination -h
      haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  refine ⟨hσv, ?_⟩
  rcases hw with hw | hw | hw
  · exact absurd (σ.injective (hw.trans hu.symm)) (Ne.symm huw)
  · exact absurd (σ.injective (hw.trans hσv.symm)) hvw.symm
  · exact hw

/-- A monic rational cubic whose discriminant is a nonzero square is cyclic or split. -/
theorem cyclic_or_splits_of_discr (ha : P.a = 1) {d : ℚ} (hd : P.discr = d ^ 2) (hd0 : d ≠ 0) :
    HasCyclicCubicGaloisGroup P.toPoly ∨ P.toPoly.Splits := by
  let L := P.toPoly.SplittingField
  have hsL : (P.toPoly.map (algebraMap ℚ L)).Splits := SplittingField.splits P.toPoly
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three (a_ne_zero ha)).mp hsL
  have hne : P.toPoly.map (algebraMap ℚ L) ≠ 0 :=
    map_ne_zero (_root_.Cubic.ne_zero_of_a_ne_zero (a_ne_zero ha))
  have hroot : ∀ r : L, aeval r P.toPoly = 0 ↔ r = x ∨ r = y ∨ r = z := by
    intro r
    have h := congrArg (r ∈ ·) h3
    simp only [_root_.Cubic.roots, _root_.Cubic.map_toPoly, mem_roots hne, IsRoot.def,
      eval_map_algebraMap, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at h
    exact h.to_iff
  set δ : L := (x - y) * (x - z) * (y - z) with hδdef
  have hδ : algebraMap ℚ L P.discr = δ ^ 2 := by
    have := _root_.Cubic.discr_eq_prod_three_roots (a_ne_zero ha) h3
    simpa [ha, δ, mul_assoc] using this
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, hd] at hδ
    exact hd0 (pow_eq_zero_iff two_ne_zero |>.mp ((algebraMap ℚ L).injective (by simpa using hδ)))
  have hfix : ∀ σ : P.toPoly.Gal, σ δ = δ := by
    intro σ
    have hsq : δ ^ 2 = (algebraMap ℚ L d) ^ 2 := by rw [← hδ, hd, map_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> rw [h] <;> simp
  -- a Galois element fixing one root is the identity
  have hext : ∀ σ : P.toPoly.Gal, σ x = x → σ y = y → σ z = z → σ = 1 := by
    intro σ hx hy hz
    apply Polynomial.Gal.ext
    intro r hr
    rw [mem_rootSet] at hr
    rcases (hroot r).mp hr.2 with rfl | rfl | rfl <;> simpa
  have hx1 : ∀ σ : P.toPoly.Gal, σ x = x → σ = 1 := fun σ hx => by
    obtain ⟨hy, hz⟩ := eq_one_of_fix σ hroot (hfix σ) hδ0 hx
    exact hext σ hx hy hz
  have hy1 : ∀ σ : P.toPoly.Gal, σ y = y → σ = 1 := fun σ hy => by
    obtain ⟨hx, hz⟩ := eq_one_of_fix (u := y) (v := x) (w := z) σ
      (fun r => (hroot r).trans (by tauto)) (by rw [show (y - x) * (y - z) * (x - z) = -δ by ring,
        map_neg, hfix]) (by rw [show (y - x) * (y - z) * (x - z) = -δ by ring]; exact neg_ne_zero.mpr hδ0) hy
    exact hext σ hx hy hz
  have hz1 : ∀ σ : P.toPoly.Gal, σ z = z → σ = 1 := fun σ hz => by
    obtain ⟨hx, hy⟩ := eq_one_of_fix (u := z) (v := x) (w := y) σ
      (fun r => (hroot r).trans (by tauto)) (by rw [show (z - x) * (z - y) * (x - y) = δ by ring,
        hfix]) (by rw [show (z - x) * (z - y) * (x - y) = δ by ring]; exact hδ0) hz
    exact hext σ hx hy hz
  have hmap : ∀ (σ : P.toPoly.Gal) r, (r = x ∨ r = y ∨ r = z) → (σ r = x ∨ σ r = y ∨ σ r = z) :=
    fun σ r hr => (hroot _).mp (by rw [aeval_algHom_apply σ, (hroot r).mpr hr, map_zero])
  -- `σ ↦ σ x` is injective, so the Galois group has at most three elements
  have hinj : Function.Injective (fun σ : P.toPoly.Gal => σ x) := by
    intro σ τ h
    have : τ⁻¹ * σ = 1 := hx1 _ (by
      simp only at h
      rw [AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
    exact (inv_mul_eq_one.mp this).symm
  have hle : Fintype.card P.toPoly.Gal ≤ 3 := by
    classical
    calc Fintype.card P.toPoly.Gal = (Finset.univ.image (fun σ : P.toPoly.Gal => σ x)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ ({x, y, z} : Finset L).card := Finset.card_le_card (by
          intro r hr
          obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hr
          rcases hmap σ x (Or.inl rfl) with h | h | h <;> simp [h])
      _ ≤ 3 := Finset.card_le_three
  -- no element of order two
  have hnot2 : Fintype.card P.toPoly.Gal ≠ 2 := by
    intro h2
    obtain ⟨σ, hσ⟩ : ∃ σ : P.toPoly.Gal, σ ≠ 1 := by
      by_contra hall
      push_neg at hall
      have : Fintype.card P.toPoly.Gal ≤ 1 :=
        Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
      omega
    have hsq : σ ^ 2 = 1 := by rw [← h2]; exact pow_card_eq_one
    have hσσ : ∀ r, σ (σ r) = r := fun r => by
      rw [← AlgEquiv.mul_apply, ← sq, hsq, AlgEquiv.one_apply]
    rcases hmap σ x (Or.inl rfl) with h | h | h
    · exact hσ (hx1 σ h)
    · -- `σ` swaps `x` and `y`, so it fixes `z`
      have hyx : σ y = x := by rw [← h, hσσ]
      rcases hmap σ z (Or.inr (Or.inr rfl)) with h' | h' | h'
      · exact absurd (σ.injective (h'.trans hyx.symm)) (fun e => hδ0 (by rw [hδdef, e]; ring))
      · exact absurd (σ.injective (h'.trans h.symm)) (fun e => hδ0 (by rw [hδdef, e]; ring))
      · exact hσ (hz1 σ h')
    · have hzx : σ z = x := by rw [← h, hσσ]
      rcases hmap σ y (Or.inr (Or.inl rfl)) with h' | h' | h'
      · exact absurd (σ.injective (h'.trans hzx.symm)) (fun e => hδ0 (by rw [hδdef, e]; ring))
      · exact hσ (hy1 σ h')
      · exact absurd (σ.injective (h'.trans h.symm)) (fun e => hδ0 (by rw [hδdef, e]; ring))
  have hpos : 0 < Fintype.card P.toPoly.Gal := Fintype.card_pos
  rcases (by omega : Fintype.card P.toPoly.Gal = 1 ∨ Fintype.card P.toPoly.Gal = 3) with h | h
  · exact Or.inr (splits_of_card_one _ h)
  · exact Or.inl ⟨mulEquivOfPrimeCardEq (p := 3)
      (by simpa only [Nat.card_eq_fintype_card] using h) (by simp [Nat.card_eq_fintype_card])⟩

end Cubic.Counting.CubicDiscriminantSquare
