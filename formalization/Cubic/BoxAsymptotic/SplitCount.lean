import Cubic.BoxAsymptotic.SquareDiscriminant
import Cubic.Counting.TraceZeroSplitCount
import Cubic.BoxAsymptotic.LatticeSums
import Cubic.BoxAsymptotic.SectorBound

/-!
# The split-polynomial subtraction is `O(H log² H)`

A monic integral cubic that splits over `ℚ` has integral roots `p, q, t` (rational root
theorem), with `a₂ = -(p + q + t)`, `a₁ = pq + pt + qt`, `a₀ = -pqt`. In the box,
`|pqt| ≤ H`; if one root vanishes, the other two satisfy `|qt| ≤ H` and `|q + t| ≤ H`.
The number of nonzero integer triples with `|p||q||t| ≤ H` is at most
`Σ_{p,q} 2H/(|p||q|) ≤ 8H(1 + log H)²`, and the cases with a zero root contribute
`O(H log H)`. The draft uses the Mahler measure and the ternary divisor estimate;
the constant term alone gives the same ternary count here.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.SplitCount

open Polynomial Cubic.Counting.GeneralMonicData Cubic.BoxAsymptotic.SquareDiscriminant
open Cubic.BoxAsymptotic.LatticeSums (sum_inv_le)

/-- `#{t : 0 < |t| ≤ Y} ≤ 2Y`. -/
theorem card_abs_le (M : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    (((Finset.Icc (-(M : ℤ)) M).filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ Y).card : ℝ) ≤ 2 * Y := by
  set F := (Finset.Icc (-(M : ℤ)) M).filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ Y
  have hsub : F ⊆ Finset.Icc (-(⌊Y⌋₊ : ℤ)) (-1) ∪ Finset.Icc 1 (⌊Y⌋₊ : ℤ) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨-, h0, hY'⟩ := ht
    have hf : |t| ≤ (⌊Y⌋₊ : ℤ) := by
      have : (|t| : ℤ).toNat ≤ ⌊Y⌋₊ := Nat.le_floor (by
        rw [show (((|t| : ℤ).toNat : ℕ) : ℝ) = ((|t| : ℤ) : ℝ) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg t)], Int.cast_abs]
        exact hY')
      omega
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    rcases lt_or_gt_of_ne h0 with h | h
    · left; rw [abs_of_neg h] at hf; omega
    · right; rw [abs_of_pos h] at hf; omega
  calc (F.card : ℝ) ≤ ((Finset.Icc (-(⌊Y⌋₊ : ℤ)) (-1) ∪ Finset.Icc 1 (⌊Y⌋₊ : ℤ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.Icc (-(⌊Y⌋₊ : ℤ)) (-1)).card + (Finset.Icc 1 (⌊Y⌋₊ : ℤ)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ = 2 * (⌊Y⌋₊ : ℝ) := by
        have hc : (Finset.Icc (-(⌊Y⌋₊ : ℤ)) (-1)).card + (Finset.Icc 1 (⌊Y⌋₊ : ℤ)).card =
            2 * ⌊Y⌋₊ := by
          simp only [Int.card_Icc]; omega
        exact_mod_cast hc
    _ ≤ 2 * Y := by linarith [Nat.floor_le hY]

/-- `Σ_{0 < |p| ≤ M} 1/|p| ≤ 2(1 + log M)`. -/
theorem sum_inv_abs (M : ℕ) :
    ∑ p ∈ (Finset.Icc (-(M : ℤ)) M).filter (· ≠ 0), (1 / |(p : ℝ)|) ≤ 2 * (1 + Real.log M) := by
  have hsplit : (Finset.Icc (-(M : ℤ)) M).filter (· ≠ 0) =
      (Finset.Icc (1 : ℤ) M).map ⟨Neg.neg, neg_injective⟩ ∪ Finset.Icc (1 : ℤ) M := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h0⟩
      rcases lt_or_gt_of_ne h0 with h | h
      · left; exact ⟨-p, ⟨by omega, by omega⟩, by ring⟩
      · right; omega
    · rintro (⟨q, ⟨h1, h2⟩, rfl⟩ | ⟨h1, h2⟩) <;> constructor <;> (try constructor) <;> omega
  have hdisj : Disjoint ((Finset.Icc (1 : ℤ) M).map ⟨Neg.neg, neg_injective⟩)
      (Finset.Icc (1 : ℤ) M) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk] at hp hp'
    obtain ⟨q, ⟨h1, -⟩, rfl⟩ := hp
    omega
  have hpos : ∑ p ∈ Finset.Icc (1 : ℤ) M, (1 / |(p : ℝ)|) = ∑ g ∈ Finset.Icc 1 M, (1 / (g : ℝ)) := by
    refine Finset.sum_nbij' (fun p => p.toNat) (fun g => (g : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_Icc] at hp ⊢; omega
    · intro g hg; simp only [Finset.mem_Icc] at hg ⊢; omega
    · intro p hp; simp only [Finset.mem_Icc] at hp; dsimp only; omega
    · intro g _; simp
    · intro p hp
      simp only [Finset.mem_Icc] at hp
      rw [abs_of_pos (by exact_mod_cast (by omega : (0 : ℤ) < p) : (0 : ℝ) < p)]
      congr 1
      rw [show ((p.toNat : ℕ) : ℝ) = ((p.toNat : ℤ) : ℝ) by push_cast; rfl, Int.toNat_of_nonneg
        (by omega)]
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Int.cast_neg, abs_neg]
  rw [hpos]
  have := sum_inv_le M
  linarith


open Cubic.BoxAsymptotic.SectorBound (card_filter_product)

/-- `#{(x, y) ∈ [-M, M]² : |x||y| ≤ H} ≤ 4H(1 + log M) + 2(2M + 1)`. -/
theorem card_pairs (M : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    ((((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).filter
      fun x : ℤ × ℤ => |(x.1 : ℝ)| * |(x.2 : ℝ)| ≤ H).card : ℝ) ≤
      4 * H * (1 + Real.log M) + 2 * (2 * M + 1) := by
  classical
  set B := Finset.Icc (-(M : ℤ)) M
  have hB : (B.card : ℝ) = 2 * M + 1 := by
    simp only [B, Int.card_Icc]
    rw [show ((M : ℤ) + 1 - -(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  rw [card_filter_product]
  push_cast
  have hx : ∀ x ∈ B, (((B.filter fun y : ℤ => |(x : ℝ)| * |(y : ℝ)| ≤ H)).card : ℝ) ≤
      (if x = 0 then (B.card : ℝ) else 0) + (if x ≠ 0 then 2 * H * (1 / |(x : ℝ)|) else 0) +
        (if x ≠ 0 then 1 else 0) := by
    intro x _
    by_cases h0 : x = 0
    · simp only [h0, if_true, ne_eq, not_true_eq_false, if_false, add_zero]
      exact_mod_cast Finset.card_filter_le _ _
    · simp only [h0, if_false, ne_eq, not_false_eq_true, if_true, zero_add]
      have hxpos : (0 : ℝ) < |(x : ℝ)| := by positivity
      have hsub : (B.filter fun y : ℤ => |(x : ℝ)| * |(y : ℝ)| ≤ H) ⊆
          (B.filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ H / |(x : ℝ)|) ∪ {0} := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
        by_cases hy0 : y = 0
        · right; exact hy0
        · left
          refine ⟨hy.1, hy0, ?_⟩
          rw [le_div_iff₀ hxpos, mul_comm]; exact hy.2
      calc (((B.filter fun y : ℤ => |(x : ℝ)| * |(y : ℝ)| ≤ H)).card : ℝ)
          ≤ (((B.filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ H / |(x : ℝ)|) ∪ {0}).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ((B.filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ H / |(x : ℝ)|).card : ℝ) + 1 := by
            exact_mod_cast Finset.card_union_le _ _
        _ ≤ 2 * (H / |(x : ℝ)|) + 1 := by
            linarith [card_abs_le M (by positivity : 0 ≤ H / |(x : ℝ)|)]
        _ = 2 * H * (1 / |(x : ℝ)|) + 1 := by ring
  refine (Finset.sum_le_sum hx).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' B 0,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum]
  have h0 : (0 : ℤ) ∈ B := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [if_pos h0, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hs := sum_inv_abs M
  have hf : (((B.filter fun x : ℤ => x ≠ 0)).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have : 2 * H * ∑ x ∈ B.filter (fun x : ℤ => x ≠ 0), (1 / |(x : ℝ)|) ≤
      2 * H * (2 * (1 + Real.log M)) := mul_le_mul_of_nonneg_left hs (by positivity)
  linarith


/-- Nonzero triples with `|p||q||t| ≤ H`: at most `8H(1 + log M)²`. -/
theorem card_triples (M : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    ((((Finset.Icc (-(M : ℤ)) M) ×ˢ ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M))).filter
      fun x : ℤ × ℤ × ℤ => x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 ∧
        |(x.1 : ℝ)| * |(x.2.1 : ℝ)| * |(x.2.2 : ℝ)| ≤ H).card : ℝ) ≤
      8 * H * (1 + Real.log M) ^ 2 := by
  classical
  set B := Finset.Icc (-(M : ℤ)) M
  rw [card_filter_product]
  push_cast
  have hinner : ∀ p ∈ B, ∀ q ∈ B, (((B.filter fun t : ℤ => p ≠ 0 ∧ q ≠ 0 ∧ t ≠ 0 ∧
      |(p : ℝ)| * |(q : ℝ)| * |(t : ℝ)| ≤ H)).card : ℝ) ≤
      if p ≠ 0 ∧ q ≠ 0 then 2 * H * ((1 / |(p : ℝ)|) * (1 / |(q : ℝ)|)) else 0 := by
    intro p _ q _
    by_cases h : p ≠ 0 ∧ q ≠ 0
    · rw [if_pos h]
      have hpq : (0 : ℝ) < |(p : ℝ)| * |(q : ℝ)| := by
        have := h.1; have := h.2; positivity
      have hsub : (B.filter fun t : ℤ => p ≠ 0 ∧ q ≠ 0 ∧ t ≠ 0 ∧
          |(p : ℝ)| * |(q : ℝ)| * |(t : ℝ)| ≤ H) ⊆
          B.filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ H / (|(p : ℝ)| * |(q : ℝ)|) := by
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        refine ⟨ht.1, ht.2.2.2.1, ?_⟩
        rw [le_div_iff₀ hpq, mul_comm]; exact ht.2.2.2.2
      calc _ ≤ ((B.filter fun t : ℤ => t ≠ 0 ∧ |(t : ℝ)| ≤ H / (|(p : ℝ)| * |(q : ℝ)|)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 * (H / (|(p : ℝ)| * |(q : ℝ)|)) := card_abs_le M (by positivity)
        _ = _ := by field_simp
    · rw [if_neg h]
      have : (B.filter fun t : ℤ => p ≠ 0 ∧ q ≠ 0 ∧ t ≠ 0 ∧
          |(p : ℝ)| * |(q : ℝ)| * |(t : ℝ)| ≤ H) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun t _ ht => h ⟨ht.1, ht.2.1⟩
      rw [this]; simp
  calc ∑ p ∈ B, (((B ×ˢ B).filter fun y : ℤ × ℤ => p ≠ 0 ∧ y.1 ≠ 0 ∧ y.2 ≠ 0 ∧
        |(p : ℝ)| * |(y.1 : ℝ)| * |(y.2 : ℝ)| ≤ H).card : ℝ)
      = ∑ p ∈ B, ∑ q ∈ B, (((B.filter fun t : ℤ => p ≠ 0 ∧ q ≠ 0 ∧ t ≠ 0 ∧
          |(p : ℝ)| * |(q : ℝ)| * |(t : ℝ)| ≤ H)).card : ℝ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [card_filter_product]; push_cast; rfl
    _ ≤ ∑ p ∈ B, ∑ q ∈ B,
        (if p ≠ 0 ∧ q ≠ 0 then 2 * H * ((1 / |(p : ℝ)|) * (1 / |(q : ℝ)|)) else 0) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hinner p hp q hq
    _ = 2 * H * ((∑ p ∈ B.filter (· ≠ 0), (1 / |(p : ℝ)|)) *
          (∑ q ∈ B.filter (· ≠ 0), (1 / |(q : ℝ)|))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        by_cases hp : p ≠ 0
        · rw [if_pos hp]
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases hq : q ≠ 0
          · rw [if_pos ⟨hp, hq⟩, if_pos hq]
          · rw [if_neg (fun h => hq h.2), if_neg hq]
        · rw [if_neg hp]
          exact Finset.sum_eq_zero fun q _ => if_neg fun h => hp h.1
    _ ≤ 2 * H * ((2 * (1 + Real.log M)) * (2 * (1 + Real.log M))) := by
        have h1 := sum_inv_abs M
        have h0 : 0 ≤ ∑ p ∈ B.filter (· ≠ 0), (1 / |(p : ℝ)|) :=
          Finset.sum_nonneg fun p _ => by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h1 h0 (by linarith)) (by positivity)
    _ = 8 * H * (1 + Real.log M) ^ 2 := by ring


/-- A split box cubic has integral roots `p, q, t`. -/
theorem roots_of_split {H : ℝ} {f : ℤ[X]} (hf : f ∈ splitSet H) :
    ∃ p q t : ℤ, f = monicCubic (-(p + q + t)) (p * q + p * t + q * t) (-(p * q * t)) ∧
      |((p + q + t : ℤ) : ℝ)| ≤ H ∧ |((p * q + p * t + q * t : ℤ) : ℝ)| ≤ H ∧
      |((p * q * t : ℤ) : ℝ)| ≤ H := by
  obtain ⟨a₂, a₁, a₀, rfl, h2, h1, h0, -, hs⟩ := hf
  set P : _root_.Cubic ℚ := ⟨1, a₂, a₁, a₀⟩
  have ha : P.a ≠ 0 := one_ne_zero
  have hP : P.toPoly = (monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ) := by
    simp [P, _root_.Cubic.toPoly, monicCubic]
  have hs' : (P.toPoly.map (RingHom.id ℚ)).Splits := by rw [Polynomial.map_id, hP]; exact hs
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three ha).mp hs'
  have hb := _root_.Cubic.b_eq_three_roots ha h3
  have hc := _root_.Cubic.c_eq_three_roots ha h3
  have hd := _root_.Cubic.d_eq_three_roots ha h3
  simp only [P, RingHom.id_apply, one_mul] at hb hc hd
  have hint : ∀ r : ℚ, r ∈ ({x, y, z} : Multiset ℚ) → ∃ m : ℤ, (m : ℚ) = r := by
    intro r hr
    rw [← h3, _root_.Cubic.roots, _root_.Cubic.map_toPoly, Polynomial.map_id,
      hP, mem_roots ((Cubic.Counting.TraceZeroSplitCount.monicCubic_monic _ _ _).map _).ne_zero,
      IsRoot.def] at hr
    have hr' : aeval r (monicCubic a₂ a₁ a₀) = 0 := by
      rw [aeval_def, ← hr, eval_map]; rfl
    obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic
      (Cubic.Counting.TraceZeroSplitCount.monicCubic_monic a₂ a₁ a₀) hr'
    exact ⟨m, hm⟩
  obtain ⟨p, rfl⟩ := hint x (by simp)
  obtain ⟨q, rfl⟩ := hint y (by simp)
  obtain ⟨t, rfl⟩ := hint z (by simp)
  have e2 : a₂ = -(p + q + t) := by exact_mod_cast (by linarith :
    ((a₂ : ℤ) : ℚ) = -(p + q + t))
  have e1 : a₁ = p * q + p * t + q * t := by exact_mod_cast (by linarith :
    ((a₁ : ℤ) : ℚ) = p * q + p * t + q * t)
  have e0 : a₀ = -(p * q * t) := by exact_mod_cast (by linarith :
    ((a₀ : ℤ) : ℚ) = -(p * q * t))
  refine ⟨p, q, t, by rw [e2, e1, e0], ?_, ?_, ?_⟩
  · rw [← abs_neg, show -((p + q + t : ℤ) : ℝ) = ((a₂ : ℤ) : ℝ) by rw [e2]; push_cast; ring]
    exact_mod_cast h2
  · rw [show ((p * q + p * t + q * t : ℤ) : ℝ) = ((a₁ : ℤ) : ℝ) by rw [e1]]
    exact_mod_cast h1
  · rw [← abs_neg, show -((p * q * t : ℤ) : ℝ) = ((a₀ : ℤ) : ℝ) by rw [e0]; push_cast; ring]
    exact_mod_cast h0

/-- A root is at most `H` in size. -/
theorem abs_root_le {p q t : ℤ} {H : ℝ} (h2 : |((p + q + t : ℤ) : ℝ)| ≤ H)
    (h1 : |((p * q + p * t + q * t : ℤ) : ℝ)| ≤ H) (h0 : |((p * q * t : ℤ) : ℝ)| ≤ H) :
    |(p : ℝ)| ≤ H := by
  rw [← Int.cast_abs] at h2 h1 h0 ⊢
  by_cases hq : q = 0
  · subst hq
    by_cases ht : t = 0
    · subst ht; simpa using h2
    · have : |p| ≤ |p * t| := by
        rw [abs_mul]; exact le_mul_of_one_le_right (abs_nonneg p) (Int.one_le_abs ht)
      simp only [mul_zero, zero_mul, add_zero, zero_add] at h1
      exact le_trans (by exact_mod_cast this) h1
  · by_cases ht : t = 0
    · subst ht
      have : |p| ≤ |p * q| := by
        rw [abs_mul]; exact le_mul_of_one_le_right (abs_nonneg p) (Int.one_le_abs hq)
      simp only [mul_zero, add_zero] at h1
      exact le_trans (by exact_mod_cast this) h1
    · have : |p| ≤ |p * q * t| := by
        rw [abs_mul, abs_mul, mul_assoc]
        exact le_mul_of_one_le_right (abs_nonneg p)
          (one_le_mul_of_one_le_of_one_le (Int.one_le_abs hq) (Int.one_le_abs ht))
      exact le_trans (by exact_mod_cast this) h0


/-- **The split-polynomial subtraction**: `#split(H) ≤ 216 H (log H)²` for `H ≥ 2`. -/
theorem split_count {H : ℝ} (hH : 2 ≤ H) :
    (Nat.card (splitSet H) : ℝ) ≤ 216 * H * Real.log H ^ 2 := by
  classical
  set M := ⌊H⌋₊
  set B := Finset.Icc (-(M : ℤ)) M
  have hH0 : 0 ≤ H := by linarith
  have hmemB : ∀ x : ℤ, |(x : ℝ)| ≤ H → x ∈ B := fun x hx => by
    have : |x| ≤ (M : ℤ) := by
      have : (|x|).toNat ≤ M := Nat.le_floor (by
        rw [show (((|x|).toNat : ℕ) : ℝ) = ((|x| : ℤ) : ℝ) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg x)], Int.cast_abs]
        exact hx)
      omega
    rw [Finset.mem_Icc]; constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
  set T := (B ×ˢ (B ×ˢ B)).filter fun x : ℤ × ℤ × ℤ =>
    |((x.1 + x.2.1 + x.2.2 : ℤ) : ℝ)| ≤ H ∧
      |((x.1 * x.2.1 + x.1 * x.2.2 + x.2.1 * x.2.2 : ℤ) : ℝ)| ≤ H ∧
      |((x.1 * x.2.1 * x.2.2 : ℤ) : ℝ)| ≤ H
  choose! fp fq ft hroots using fun f (hf : f ∈ splitSet H) => roots_of_split hf
  have hall : ∀ p q t : ℤ, |((p + q + t : ℤ) : ℝ)| ≤ H →
      |((p * q + p * t + q * t : ℤ) : ℝ)| ≤ H → |((p * q * t : ℤ) : ℝ)| ≤ H →
      (p, q, t) ∈ T := by
    intro p q t h2 h1 h0
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨hmemB p (abs_root_le h2 h1 h0), hmemB q (abs_root_le (q := p) (t := t) ?_ ?_ ?_),
      hmemB t (abs_root_le (q := p) (t := q) ?_ ?_ ?_)⟩, h2, h1, h0⟩
    all_goals first
      | (rw [show (q + p + t : ℤ) = p + q + t by ring]; exact h2)
      | (rw [show (q * p + q * t + p * t : ℤ) = p * q + p * t + q * t by ring]; exact h1)
      | (rw [show (q * p * t : ℤ) = p * q * t by ring]; exact h0)
      | (rw [show (t + p + q : ℤ) = p + q + t by ring]; exact h2)
      | (rw [show (t * p + t * q + p * q : ℤ) = p * q + p * t + q * t by ring]; exact h1)
      | (rw [show (t * p * q : ℤ) = p * q * t by ring]; exact h0)
  have hcardT : Nat.card (splitSet H) ≤ T.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun f => (fp f, fq f, ft f)) (fun f hf => ?_)
      (fun f hf g hg hfg => ?_) (Finset.finite_toSet T)
    · obtain ⟨-, h2, h1, h0⟩ := hroots f hf
      exact hall _ _ _ h2 h1 h0
    · simp only [Prod.mk.injEq] at hfg
      rw [(hroots f hf).1, (hroots g hg).1, hfg.1, hfg.2.1, hfg.2.2]
  -- split `T` by zero coordinates
  set P2 := (B ×ˢ B).filter fun x : ℤ × ℤ => |(x.1 : ℝ)| * |(x.2 : ℝ)| ≤ H
  set T3 := (B ×ˢ (B ×ˢ B)).filter fun x : ℤ × ℤ × ℤ => x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 ∧
    |(x.1 : ℝ)| * |(x.2.1 : ℝ)| * |(x.2.2 : ℝ)| ≤ H
  have hsub : T ⊆ T3 ∪ ((T.filter fun x => x.1 = 0) ∪ ((T.filter fun x => x.2.1 = 0) ∪
      (T.filter fun x => x.2.2 = 0))) := by
    intro x hx
    by_cases h1 : x.1 = 0
    · simp [Finset.mem_union, Finset.mem_filter, hx, h1]
    by_cases h2 : x.2.1 = 0
    · simp [Finset.mem_union, Finset.mem_filter, hx, h2]
    by_cases h3 : x.2.2 = 0
    · simp [Finset.mem_union, Finset.mem_filter, hx, h3]
    refine Finset.mem_union_left _ ?_
    have hx' := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hx'.1, h1, h2, h3, ?_⟩
    have := hx'.2.2.2
    rw [Int.cast_mul, Int.cast_mul, abs_mul, abs_mul] at this
    exact this
  have hz : ∀ (g : ℤ × ℤ × ℤ → ℤ × ℤ) (c : ℤ × ℤ × ℤ → ℤ),
      Set.InjOn g ↑(T.filter fun x => c x = 0) →
      (∀ x ∈ T.filter (fun x => c x = 0), g x ∈ P2) →
      (T.filter fun x => c x = 0).card ≤ P2.card := fun g c hg hm =>
    Finset.card_le_card_of_injOn g (fun x hx => hm x hx) hg
  have hz1 : (T.filter fun x => x.1 = 0).card ≤ P2.card := by
    refine hz (fun x => (x.2.1, x.2.2)) (fun x => x.1) (fun x hx y hy h => ?_) (fun x hx => ?_)
    · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (hx.2.trans hy.2.symm) (Prod.ext h.1 h.2)
    · rw [Finset.mem_filter] at hx
      obtain ⟨hxT, h0⟩ := hx
      have hxT' := Finset.mem_filter.mp hxT
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp
        (Finset.mem_product.mp hxT'.1).2).1, (Finset.mem_product.mp
        (Finset.mem_product.mp hxT'.1).2).2⟩, ?_⟩
      have := hxT'.2.2.1
      simp only at h0
      rw [h0] at this
      simpa [abs_mul] using this
  have hz2 : (T.filter fun x => x.2.1 = 0).card ≤ P2.card := by
    refine hz (fun x => (x.1, x.2.2)) (fun x => x.2.1) (fun x hx y hy h => ?_) (fun x hx => ?_)
    · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext (hx.2.trans hy.2.symm) h.2)
    · rw [Finset.mem_filter] at hx
      obtain ⟨hxT, h0⟩ := hx
      have hxT' := Finset.mem_filter.mp hxT
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hxT'.1).1,
        (Finset.mem_product.mp (Finset.mem_product.mp hxT'.1).2).2⟩, ?_⟩
      have := hxT'.2.2.1
      simp only at h0
      rw [h0] at this
      simpa [abs_mul] using this
  have hz3 : (T.filter fun x => x.2.2 = 0).card ≤ P2.card := by
    refine hz (fun x => (x.1, x.2.1)) (fun x => x.2.2) (fun x hx y hy h => ?_) (fun x hx => ?_)
    · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 (hx.2.trans hy.2.symm))
    · rw [Finset.mem_filter] at hx
      obtain ⟨hxT, h0⟩ := hx
      have hxT' := Finset.mem_filter.mp hxT
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hxT'.1).1,
        (Finset.mem_product.mp (Finset.mem_product.mp hxT'.1).2).1⟩, ?_⟩
      have := hxT'.2.2.1
      simp only at h0
      rw [h0] at this
      simpa [abs_mul] using this
  have hT : (T.card : ℝ) ≤ T3.card + 3 * P2.card := by
    have a := Finset.card_le_card hsub
    have b := Finset.card_union_le T3 ((T.filter fun x => x.1 = 0) ∪
      ((T.filter fun x => x.2.1 = 0) ∪ (T.filter fun x => x.2.2 = 0)))
    have c := Finset.card_union_le (T.filter fun x => x.1 = 0)
      ((T.filter fun x => x.2.1 = 0) ∪ (T.filter fun x => x.2.2 = 0))
    have d := Finset.card_union_le (T.filter fun x => x.2.1 = 0) (T.filter fun x => x.2.2 = 0)
    have : T.card ≤ T3.card + 3 * P2.card := by omega
    exact_mod_cast this
  have h3 := card_triples M hH0
  have h2 := card_pairs M hH0
  -- logarithms
  have hL : 1 ≤ 2 * Real.log H := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.le_floor (by norm_num; linarith : ((1 : ℕ) : ℝ) ≤ H)
  have hMH : (M : ℝ) ≤ H := Nat.floor_le hH0
  have hlogM : Real.log M ≤ Real.log H := Real.log_le_log (by linarith) hMH
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hl1 : 1 + Real.log M ≤ 3 * Real.log H := by linarith
  have hsq : (1 + Real.log M) ^ 2 ≤ (3 * Real.log H) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hl1 2
  have hLpos : 0 ≤ Real.log H := by linarith
  calc (Nat.card (splitSet H) : ℝ) ≤ T.card := by exact_mod_cast hcardT
    _ ≤ T3.card + 3 * P2.card := hT
    _ ≤ 8 * H * (1 + Real.log M) ^ 2 + 3 * (4 * H * (1 + Real.log M) + 2 * (2 * M + 1)) := by
        linarith
    _ ≤ 216 * H * Real.log H ^ 2 := by
        have e1 : 8 * H * (1 + Real.log M) ^ 2 ≤ 72 * H * Real.log H ^ 2 := by nlinarith
        have hL2 : Real.log H ≤ 2 * Real.log H ^ 2 := by nlinarith
        have hL3 : 1 ≤ 4 * Real.log H ^ 2 := by nlinarith
        have e2 : 4 * H * (1 + Real.log M) ≤ 24 * H * Real.log H ^ 2 := by
          have a := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 4 * H)
          have b := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ 12 * H)
          linarith
        have e3 : 2 * (2 * (M : ℝ) + 1) ≤ 24 * H * Real.log H ^ 2 := by
          have b := mul_le_mul_of_nonneg_left hL3 (by positivity : (0 : ℝ) ≤ 6 * H)
          linarith
        linarith

end Cubic.BoxAsymptotic.SplitCount
