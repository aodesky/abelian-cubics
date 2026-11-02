import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing the split or cyclic cubic Galois group

A Galois group of cardinality at most three whose elements cube to one is
trivial or cyclic of order three. In the trivial case the original polynomial
splits over the ground field, by the fixed-field theorem.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SmallGaloisGroup

open Polynomial CorrespondencePolynomials

theorem splits_of_card_one (f : ℚ[X]) (h : Fintype.card f.Gal = 1) : f.Splits := by
  haveI : Subsingleton f.Gal := Fintype.card_le_one_iff_subsingleton.mp h.le
  haveI : IsGalois ℚ f.SplittingField := ⟨⟩
  apply Polynomial.Splits.of_splits_map (algebraMap ℚ f.SplittingField)
    (Polynomial.SplittingField.splits f)
  intro x _
  apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
  intro σ
  exact congrArg (fun τ : f.Gal => τ x) (@Subsingleton.elim f.Gal inferInstance σ 1)

theorem cyclic_or_splits (f : ℚ[X]) (hcard : Fintype.card f.Gal ≤ 3)
    (hcube : ∀ σ : f.Gal, σ ^ 3 = 1) : HasCyclicCubicGaloisGroup f ∨ f.Splits := by
  have hpos : 0 < Fintype.card f.Gal := Fintype.card_pos
  have hnot_two : Fintype.card f.Gal ≠ 2 := by
    intro htwo
    have hall : ∀ σ : f.Gal, σ = 1 := by
      intro σ
      have hsq : σ ^ 2 = 1 := by simpa only [htwo] using pow_card_eq_one (x := σ)
      have h := hcube σ
      rw [pow_succ, hsq, one_mul] at h
      exact h
    haveI : Subsingleton f.Gal := ⟨fun σ τ => (hall σ).trans (hall τ).symm⟩
    have : Fintype.card f.Gal ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  have hcases : Fintype.card f.Gal = 1 ∨ Fintype.card f.Gal = 3 := by omega
  rcases hcases with h | h
  · exact Or.inr (splits_of_card_one f h)
  · left
    exact ⟨mulEquivOfPrimeCardEq (p := 3)
      (by simpa only [Nat.card_eq_fintype_card] using h)
      (by simp [Nat.card_eq_fintype_card])⟩

end Cubic.QuadraticCorrespondence.SmallGaloisGroup
