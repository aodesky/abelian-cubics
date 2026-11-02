import Cubic.AllGaloisCounts.GaloisClassification
import Cubic.AllGaloisCounts.SplitRepeated

/-! Integral roots counted without multiplicity. Quadratic Galois group
gives exactly one; a split cubic gives three except in the already bounded
family of repeated-root triples. -/

noncomputable section

namespace Cubic.AllGaloisCounts.IntegerRootCounts
open Polynomial CountData HeightBox SplitOrbits GaloisClassification
open Cubic.Counting.GeneralMonicData
open Cubic.Counting.TraceZeroSplitCount (cubicOf monicCubic_monic)

def integerRoots (f : ℤ[X]) : Finset ℤ := f.roots.toFinset

theorem degree_three {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) : f.natDegree = 3 := by
  obtain ⟨⟨a, b, c, rfl⟩, _⟩ := hf
  unfold monicCubic
  compute_degree!

theorem rational_degree_three {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) :
    (f.map (Int.castRingHom ℚ)).natDegree = 3 := by
  rw [natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)), degree_three hf]

theorem ne_zero {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) : f ≠ 0 := by
  intro he
  have hd := degree_three hf
  simp [he] at hd

theorem mem_roots {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) (r : ℤ) :
    r ∈ integerRoots f ↔ f.eval r = 0 := by
  simp only [integerRoots, Multiset.mem_toFinset, Polynomial.mem_roots (ne_zero hf), IsRoot.def]

theorem rational_root {f : ℤ[X]} {r : ℤ} (hr : f.eval r = 0) :
    (f.map (Int.castRingHom ℚ)).IsRoot (r : ℚ) := by
  rw [IsRoot.def, eval_map]
  change f.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) r) = 0
  rw [eval₂_at_apply, hr, map_zero]

theorem roots_card_le {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) : (integerRoots f).card ≤ 3 :=
  (Multiset.toFinset_card_le _).trans ((card_roots' f).trans_eq (degree_three hf))

theorem quadratic_roots {H : ℝ} {f : ℤ[X]} (hf : f ∈ galoisSet .quadratic H) :
    (integerRoots f).card = 1 := by
  obtain ⟨r, hr, hu⟩ := quadratic_unique_root (rational_degree_three hf.1) hf.2
  obtain ⟨a, b, c, he⟩ := hf.1.1
  have hm : f.Monic := he ▸ monicCubic_monic a b c
  have hr' : aeval r f = 0 := by
    simpa only [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hr
  obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic hm hr'
  change (m : ℚ) = r at hm
  have hset : integerRoots f = {m} := by
    ext n
    rw [mem_roots hf.1, Finset.mem_singleton]
    constructor
    · intro hn
      have h := (hu (n : ℚ) (rational_root hn)).trans hm.symm
      exact_mod_cast h
    · intro hn
      subst n
      have h := hr
      rw [← hm] at h
      have h' : ((f.eval m : ℤ) : ℚ) = 0 := by
        rw [IsRoot.def, eval_map] at h
        change f.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) m) = 0 at h
        rw [eval₂_at_apply] at h
        exact h
      exact_mod_cast h'
  rw [hset, Finset.card_singleton]

theorem no_roots {H : ℝ} {f : ℤ[X]} {G : GaloisType}
    (hf : f ∈ galoisSet G H) (hG : G = .cyclic ∨ G = .symmetric) : integerRoots f = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hle := card_le_two_of_root (rational_degree_three hf.1)
    (rational_root ((mem_roots hf.1 r).mp hr))
  rw [card_of_type hf.2] at hle
  rcases hG with rfl | rfl <;> norm_num [order] at hle

def exceptional (H : ℝ) : Set ℤ[X] :=
  (fun v : Triples H => cubicOf v.1) '' SplitRepeated.repeated H

theorem exceptional_finite (H : ℝ) : (exceptional H).Finite := by
  haveI : Finite (Triples H) := (triples_finite H).to_subtype
  exact (Set.toFinite (SplitRepeated.repeated H)).image _

theorem exceptional_subset (H : ℝ) : exceptional H ⊆ cubicBox H := by
  rintro f ⟨v, _, rfl⟩
  exact (cubicOf_mem v).1

theorem exceptional_bound {H : ℝ} (hH : 1 ≤ H) :
    ((exceptional H).ncard : ℝ) ≤ 75 * H ^ 2 := by
  haveI : Finite (Triples H) := (triples_finite H).to_subtype
  have h : (exceptional H).ncard ≤ (SplitRepeated.repeated H).ncard := Set.ncard_image_le
  exact (Nat.cast_le.mpr h).trans (SplitRepeated.repeated_bound hH)

theorem roots_cubicOf (v : Fin 3 → ℤ) : integerRoots (cubicOf v) = {v 0, v 1, v 2} := by
  ext r
  rw [integerRoots, Multiset.mem_toFinset, Cubic.Counting.TraceZeroSplitCount.roots_cubicOf]
  simp

theorem split_roots {H : ℝ} {f : ℤ[X]} (hf : f ∈ galoisSet .trivial H)
    (he : f ∉ exceptional H) : (integerRoots f).card = 3 := by
  obtain ⟨⟨a, b, c, rfl⟩, hH⟩ := hf.1
  obtain ⟨x, y, z, hxyz⟩ := integral_roots ((trivial_iff_splits _).mp hf.2)
  let v : Triples H := ⟨![x, y, z], by
    rw [Triples, Set.mem_setOf_eq, cubicOf_eq]
    exact hxyz ▸ hH⟩
  have hv : cubicOf v.1 = monicCubic a b c := by
    rw [cubicOf_eq]; exact hxyz.symm
  have hnr : v ∉ SplitRepeated.repeated H := fun h => he ⟨v, h, hv⟩
  change ¬(x = y ∨ x = z ∨ y = z) at hnr
  rw [← hv, roots_cubicOf]
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp [show x ≠ y from fun h => hnr (Or.inl h),
    show x ≠ z from fun h => hnr (Or.inr (Or.inl h)),
    show y ≠ z from fun h => hnr (Or.inr (Or.inr h))]

end Cubic.AllGaloisCounts.IntegerRootCounts
