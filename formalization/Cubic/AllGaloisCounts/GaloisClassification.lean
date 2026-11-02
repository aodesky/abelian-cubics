import Cubic.AllGaloisCounts.SplitOrbits
import Cubic.Counting.CyclicCubicField
import Mathlib.GroupTheory.Coset.Card

/-! The four actual splitting-field Galois groups of a rational cubic.
Irreducible cubics act transitively on three roots; a rational linear
factor reduces the Galois group to that of the remaining quadratic. -/

noncomputable section

namespace Cubic.AllGaloisCounts.GaloisClassification
open Polynomial CountData

def order : GaloisType → ℕ
  | .trivial => 1
  | .quadratic => 2
  | .cyclic => 3
  | .symmetric => 6

theorem card_of_type {f : ℚ[X]} {G : GaloisType} (h : HasGaloisType G f) :
    Nat.card f.Gal = order G := by
  cases G <;> obtain ⟨e⟩ := h <;> rw [Nat.card_congr e.toEquiv] <;>
    norm_num [order, Nat.card_eq_fintype_card, Fintype.card_perm]

theorem type_unique {f : ℚ[X]} {G J : GaloisType}
    (hG : HasGaloisType G f) (hJ : HasGaloisType J f) : G = J := by
  have h := (card_of_type hG).symm.trans (card_of_type hJ)
  cases G <;> cases J <;> simp_all [order]

theorem quadratic_of_card_two {f : ℚ[X]} (h : Nat.card f.Gal = 2) :
    HasGaloisType .quadratic f :=
  ⟨mulEquivOfPrimeCardEq (p := 2) h (by simp [Nat.card_eq_fintype_card])⟩

theorem card_le_two_of_root {f : ℚ[X]} (hd : f.natDegree = 3) {r : ℚ}
    (hr : f.IsRoot r) : Nat.card f.Gal ≤ 2 := by
  classical
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [hq] at hd
  have hqd : q.natDegree ≤ 2 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero r) hq0, natDegree_X_sub_C] at hd
    omega
  rw [hq, Nat.card_eq_fintype_card]
  haveI : Unique (X - C r).Gal := Gal.uniqueGalOfSplits _ (Splits.X_sub_C r)
  have hle := Fintype.card_le_of_injective _ (Gal.restrictProd_injective (X - C r) q)
  have h1 : Fintype.card (X - C r).Gal = 1 := Fintype.card_unique
  rw [Fintype.card_prod, h1, one_mul] at hle
  exact hle.trans (Cubic.Counting.CyclicCubicField.card_gal_le_two q hqd)

theorem irreducible_types {f : ℚ[X]} (hd : f.natDegree = 3) (hi : Irreducible f) :
    HasGaloisType .cyclic f ∨ HasGaloisType .symmetric f := by
  classical
  haveI : Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) :=
    ⟨SplittingField.splits f⟩
  have hr : Fintype.card (f.rootSet f.SplittingField) = 3 := by
    rw [card_rootSet_eq_natDegree hi.separable (SplittingField.splits f), hd]
  let e := Fintype.equivFinOfCardEq hr
  let φ : f.Gal →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (Gal.galActionHom f f.SplittingField)
  have hinj : Function.Injective φ :=
    e.permCongrHom.injective.comp (Gal.galActionHom_injective f f.SplittingField)
  have h6 : Nat.card f.Gal ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using Subgroup.card_dvd_of_injective φ hinj
  have h3 : 3 ∣ Nat.card f.Gal := by
    simpa only [hd] using Gal.prime_degree_dvd_card hi (by rw [hd]; decide)
  have hc : Nat.card f.Gal = 3 ∨ Nat.card f.Gal = 6 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 6) h6
    have hpos : 0 < Nat.card f.Gal := Nat.card_pos
    omega
  rcases hc with hc | hc
  · exact Or.inl ⟨mulEquivOfPrimeCardEq (p := 3) hc
      (by simp [Nat.card_eq_fintype_card])⟩
  · exact Or.inr ⟨MulEquiv.ofBijective φ
      ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, by
        simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using hc⟩)⟩

theorem root_of_reducible {f : ℚ[X]} (hd : f.natDegree = 3)
    (hi : ¬ Irreducible f) : ∃ r : ℚ, f.IsRoot r := by
  by_contra hr
  push_neg at hr
  exact hi (irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide) hr)

theorem reducible_types {f : ℚ[X]} (hd : f.natDegree = 3) (hi : ¬ Irreducible f) :
    HasGaloisType .trivial f ∨ HasGaloisType .quadratic f := by
  obtain ⟨r, hr⟩ := root_of_reducible hd hi
  have hc := card_le_two_of_root hd hr
  have hpos : 0 < Nat.card f.Gal := Nat.card_pos
  have he : Nat.card f.Gal = 1 ∨ Nat.card f.Gal = 2 := by omega
  rcases he with he | he
  · exact Or.inl ((SplitOrbits.trivial_iff_splits f).mpr
      (Cubic.QuadraticCorrespondence.SmallGaloisGroup.splits_of_card_one f
        (by simpa only [Nat.card_eq_fintype_card] using he)))
  · exact Or.inr (quadratic_of_card_two he)

theorem exists_type {f : ℚ[X]} (hd : f.natDegree = 3) :
    ∃ G, HasGaloisType G f := by
  by_cases hi : Irreducible f
  · rcases irreducible_types hd hi with h | h
    · exact ⟨.cyclic, h⟩
    · exact ⟨.symmetric, h⟩
  · rcases reducible_types hd hi with h | h
    · exact ⟨.trivial, h⟩
    · exact ⟨.quadratic, h⟩

theorem quadratic_reducible {f : ℚ[X]} (hd : f.natDegree = 3)
    (h : HasGaloisType .quadratic f) : ¬ Irreducible f := by
  intro hi
  rcases irreducible_types hd hi with hc | hs
  · cases type_unique h hc
  · cases type_unique h hs

theorem splits_of_two_roots {f : ℚ[X]} (hd : f.natDegree = 3) {r s : ℚ}
    (hr : f.IsRoot r) (hs : f.IsRoot s) (hne : r ≠ s) : f.Splits := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hq0 : q ≠ 0 := by rintro rfl; simp [hq] at hd
  have hqd : q.natDegree = 2 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero r) hq0, natDegree_X_sub_C] at hd
    omega
  have hqs : q.eval s = 0 := by
    rw [IsRoot.def, hq, eval_mul, eval_sub, eval_X, eval_C] at hs
    exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hne.symm)
  rw [hq]
  exact (Splits.X_sub_C r).mul (Splits.of_natDegree_eq_two hqd hqs)

theorem quadratic_unique_root {f : ℚ[X]} (hd : f.natDegree = 3)
    (h : HasGaloisType .quadratic f) : ∃! r : ℚ, f.IsRoot r := by
  obtain ⟨r, hr⟩ := root_of_reducible hd (quadratic_reducible hd h)
  refine ⟨r, hr, fun s hs => ?_⟩
  by_contra hne
  have ht := (SplitOrbits.trivial_iff_splits f).mpr (splits_of_two_roots hd hs hr hne)
  cases type_unique h ht

end Cubic.AllGaloisCounts.GaloisClassification
