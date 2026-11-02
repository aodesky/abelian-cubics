import Cubic.BoxHeight.CyclicCubicDiscriminant
import Cubic.BoxHeight.WidmerFieldCount
import Cubic.BoxHeight.XiaoCounterexample

/-!
# Summing the field counts

Supporting lemmas for `thm:lower` of `box_height_research_note.tex`. For a set `A` of nonzero
characters closed under `a ↦ -a`, the fields `K_a` (`a ∈ A`) are counted twice each, since
`K_a = K_b` exactly for `b = ±a`. Distinct fields give disjoint sets of polynomials
("Distinct cyclic cubic fields give disjoint sets of irreducible polynomials"), and the
polynomials from a field with `M(α) ≤ H/3` have box height at most `H`. Hence
`N_□(H) ≥ ½ Σ_{a ∈ A} P_{K_a}(H/3)`.
-/

noncomputable section

namespace Cubic.BoxHeight.LowerBoundFields

open NumberField Polynomial CubicTargets.BoxHeight
open Cubic.BoxHeight.FieldCount Cubic.BoxHeight.CyclicCubicCharacters
open Cubic.BoxHeight.CyclicCubicFields

variable {P : SplitSet}

/-- Distinct fields `K_a` give disjoint polynomial sets. -/
theorem disjoint_polySet {a b : ι P → ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) (hne : K P a ≠ K P b)
    (Y Y' : ℝ) : Disjoint (polySet (K P a) Y) (polySet (K P b) Y') := by
  refine Set.disjoint_left.mpr fun f h₁ h₂ => hne ?_
  obtain ⟨e⟩ := algEquiv_of_mem (finrank_K ha) (finrank_K hb) h₁ h₂
  exact K_eq_of_algEquiv e

/-- `N_□(H) ≥ Σ_{F} P_F(H/3)` over the distinct fields `F = K_a`, `a ∈ A`. -/
theorem sum_le_boxCount [DecidableEq (IntermediateField ℚ (L P))] (A : Finset (ι P → ZMod 3))
    (hA : ∀ a ∈ A, a ≠ 0) (H : ℝ) :
    ∑ F ∈ A.image (K P), Nat.card (polySet F (H / 3)) ≤ boxCount H := by
  classical
  have hfin : ∀ F : IntermediateField ℚ (L P), (polySet F (H / 3)).Finite :=
    fun F => polySet_finite _
  set T := (A.image (K P)).biUnion fun F => (hfin F).toFinset
  have hT : T.card = ∑ F ∈ A.image (K P), Nat.card (polySet F (H / 3)) := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun F _ => ?_
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (hfin F)]
    · intro F hF F' hF' hFF'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hF'
      rw [Function.onFun, Set.Finite.disjoint_toFinset]
      exact disjoint_polySet (hA a ha) (hA b hb) hFF' _ _
  rw [← hT, boxCount, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card _ (FieldCount.boxSet_finite H)]
  refine Finset.card_le_card fun f hf => ?_
  obtain ⟨F, hF, hfF⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hF
  have hsub := polySet_subset_box (finrank_K (hA a ha)) (H / 3)
  rw [show 3 * (H / 3) = H by ring] at hsub
  exact (FieldCount.boxSet_finite H).mem_toFinset.mpr
    (hsub ((hfin _).mem_toFinset.mp hfF))

theorem neg_ne_self_zmod : ∀ x : ZMod 3, x ≠ 0 → -x ≠ x := by decide

theorem neg_ne_self {a : ι P → ZMod 3} (ha : a ≠ 0) : -a ≠ a := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  exact neg_ne_self_zmod (a i) hi (congrFun h i)

/-- Each field is counted twice: `Σ_{a ∈ A} w(K_a) = 2 Σ_F w(F)`. -/
theorem sum_eq_two_mul [DecidableEq (IntermediateField ℚ (L P))] (A : Finset (ι P → ZMod 3))
    (hA : ∀ a ∈ A, a ≠ 0) (hneg : ∀ a ∈ A, -a ∈ A) (w : IntermediateField ℚ (L P) → ℝ) :
    ∑ a ∈ A, w (K P a) = 2 * ∑ F ∈ A.image (K P), w F := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := K P) (t := A.image (K P))
    (fun a ha => Finset.mem_image_of_mem _ ha), Finset.mul_sum]
  refine Finset.sum_congr rfl fun F hF => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hF
  have hfib : A.filter (fun a => K P a = K P a₀) = {a₀, -a₀} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hK⟩
      exact eq_or_eq_neg_of_K_eq (hA a₀ ha₀) (hA a ha) hK.symm
    · rintro (rfl | rfl)
      · exact ⟨ha₀, rfl⟩
      · exact ⟨hneg _ ha₀, K_neg a₀⟩
  rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2], Finset.sum_const,
    hfib, Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]; exact (neg_ne_self (hA a₀ ha₀)).symm),
    Finset.card_singleton, nsmul_eq_mul]
  norm_num

end Cubic.BoxHeight.LowerBoundFields
