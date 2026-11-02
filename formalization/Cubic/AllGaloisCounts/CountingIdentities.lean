import Cubic.AllGaloisCounts.IntegerRootCounts

/-! The disjoint Galois partition and the marked-root identity, with its
repeated-root error bounded by the actual exceptional family. -/

noncomputable section
open scoped Classical

namespace Cubic.AllGaloisCounts.CountingIdentities
open Polynomial CountData HeightBox GaloisClassification IntegerRootCounts

def box (H : ℝ) : Finset ℤ[X] := (cubicBox_finite H).toFinset

theorem mem_box (H : ℝ) (f : ℤ[X]) : f ∈ box H ↔ f ∈ cubicBox H :=
  Set.Finite.mem_toFinset _

def indicator (G : GaloisType) (f : ℤ[X]) : ℕ := by
  classical
  exact if HasGaloisType G (f.map (Int.castRingHom ℚ)) then 1 else 0

theorem type_count (G : GaloisType) (H : ℝ) :
    N G H = ∑ f ∈ box H, indicator G f := by
  classical
  have he : galoisSet G H =
      ↑((box H).filter (fun f => HasGaloisType G (f.map (Int.castRingHom ℚ)))) := by
    ext f
    simp [galoisSet, mem_box]
  rw [N, Nat.card_coe_set_eq, he, Set.ncard_coe_finset, Finset.card_filter]
  rfl

theorem indicator_partition {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) :
    indicator .trivial f + indicator .quadratic f + indicator .cyclic f +
      indicator .symmetric f = 1 := by
  obtain ⟨G, hG⟩ := exists_type (rational_degree_three hf)
  have ht : ∀ J, HasGaloisType J (f.map (Int.castRingHom ℚ)) ↔ J = G :=
    fun J => ⟨fun hJ => type_unique hJ hG, fun h => h ▸ hG⟩
  cases G <;> simp [indicator, ht]

theorem partition (H : ℝ) : Nat.card (cubicBox H) =
    N .trivial H + N .quadratic H + N .cyclic H + N .symmetric H := by
  rw [type_count, type_count, type_count, type_count,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hs : (∑ f ∈ box H, (indicator .trivial f + indicator .quadratic f +
      indicator .cyclic f + indicator .symmetric f)) = (box H).card := by
    calc _ = ∑ _f ∈ box H, 1 := Finset.sum_congr rfl
          (fun f hf => indicator_partition ((mem_box H f).mp hf))
      _ = _ := by simp
  rw [hs, box, ← Set.ncard_eq_toFinset_card _ (cubicBox_finite H), Nat.card_coe_set_eq]

theorem marked_card (H : ℝ) : markedCount H = ∑ f ∈ box H, (integerRoots f).card := by
  classical
  let s := (MarkedFactorization.markedSet_finite H).toFinset
  have hm : markedCount H = s.card := by
    rw [markedCount, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (MarkedFactorization.markedSet_finite H)]
  rw [hm, Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := box H)
    (fun fr hfr => (mem_box H fr.1).mpr
      (((Set.Finite.mem_toFinset _).mp hfr) : fr ∈ markedSet H).1)]
  apply Finset.sum_congr rfl
  intro f hf
  have hfb := (mem_box H f).mp hf
  apply Finset.card_bij (fun fr _ => fr.2)
  · intro fr hfr
    obtain ⟨hfr, he⟩ := Finset.mem_filter.mp hfr
    have hp : fr ∈ markedSet H := (Set.Finite.mem_toFinset _).mp hfr
    exact (mem_roots hfb fr.2).mpr (he ▸ hp.2)
  · intro fr hfr gr hgr he
    exact Prod.ext ((Finset.mem_filter.mp hfr).2.trans
      (Finset.mem_filter.mp hgr).2.symm) he
  · intro r hr
    refine ⟨(f, r), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    exact (Set.Finite.mem_toFinset _).mpr ⟨hfb, (mem_roots hfb r).mp hr⟩

theorem root_error {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H) :
    |((integerRoots f).card : ℝ) - indicator .quadratic f - 3 * indicator .trivial f| ≤
      3 * (if f ∈ exceptional H then 1 else 0 : ℝ) := by
  classical
  obtain ⟨G, hG⟩ := exists_type (rational_degree_three hf)
  have ht : ∀ J, HasGaloisType J (f.map (Int.castRingHom ℚ)) ↔ J = G :=
    fun J => ⟨fun hJ => type_unique hJ hG, fun h => h ▸ hG⟩
  cases G with
  | trivial =>
    simp only [indicator, ht]
    norm_num
    by_cases he : f ∈ exceptional H
    · rw [if_pos he]
      have hl : ((integerRoots f).card : ℝ) ≤ 3 := by exact_mod_cast roots_card_le hf
      rw [abs_of_nonpos (by linarith)]
      have h0 : (0 : ℝ) ≤ (integerRoots f).card := Nat.cast_nonneg _
      linarith
    · rw [if_neg he, split_roots ⟨hf, hG⟩ he]
      norm_num
  | quadratic =>
    simp only [indicator, ht, quadratic_roots ⟨hf, hG⟩]
    by_cases he : f ∈ exceptional H <;> simp [he]
  | cyclic =>
    simp only [indicator, ht, no_roots ⟨hf, hG⟩ (Or.inl rfl), Finset.card_empty]
    by_cases he : f ∈ exceptional H <;> simp [he]
  | symmetric =>
    simp only [indicator, ht, no_roots ⟨hf, hG⟩ (Or.inr rfl), Finset.card_empty]
    by_cases he : f ∈ exceptional H <;> simp [he]

theorem marked_error {H : ℝ} (hH : 1 ≤ H) :
    |(markedCount H : ℝ) - N .quadratic H - 3 * N .trivial H| ≤ 225 * H ^ 2 := by
  classical
  have he : (∑ f ∈ box H, if f ∈ exceptional H then (1 : ℝ) else 0) =
      (exceptional H).ncard := by
    have hs : (box H).filter (fun f => f ∈ exceptional H) =
        (exceptional_finite H).toFinset := by
      ext f
      simp only [Finset.mem_filter, mem_box, Set.Finite.mem_toFinset]
      exact ⟨And.right, fun hf => ⟨exceptional_subset H hf, hf⟩⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hs,
      ← Set.ncard_eq_toFinset_card _ (exceptional_finite H)]
  rw [marked_card, type_count, type_count]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ f ∈ box H,
        |((integerRoots f).card : ℝ) - indicator .quadratic f - 3 * indicator .trivial f| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ box H, 3 * (if f ∈ exceptional H then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun f hf => root_error ((mem_box H f).mp hf))
    _ = 3 * (exceptional H).ncard := by rw [← Finset.mul_sum, he]
    _ ≤ 225 * H ^ 2 := by linarith [exceptional_bound hH]

end Cubic.AllGaloisCounts.CountingIdentities
