import Cubic.BoxAsymptotic.Cells
import Cubic.BoxAsymptotic.GoodCount

/-!
# The discarded region (`lem:geometry`, part 4)

A pair off the core has `n ≤ 3`, or `B = 0`, or lies in a band `X = 2^i` either in the
critical sector `τ ≤ T_c` or in a dyadic cell `T_k = T_c 2^k` that is *bad*:

  `T_k > ε/16`, or `ε² T_k² X √X < 46000 H`, or `H/(128X) < T_k ≤ 17H/X`, or `64X > H²`

(the last two use `W ≠ 0`, which forces `τ ≤ 17H/X` for `X ≥ H`). Each band has
`O(1 + log(1/ε))` bad cells, and `O(log H)` in the `O(1)` bands with `64 X > H²`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Discard

open Real
open Cubic.BoxAsymptotic.Admissible (Bset θ mem_Bset Nmax)
open Cubic.BoxAsymptotic.Bands (band band_bounds)
open Cubic.BoxAsymptotic.TraceWidth (W E W_nonneg W_le_sqrt)
open Cubic.BoxAsymptotic.Pieces (τof)
open Cubic.BoxAsymptotic.Core (InCore tau_sum)
open Cubic.BoxAsymptotic.Cells
open scoped Classical

/-- A bad cell. -/
def BadCell (H ε X T : ℝ) : Prop :=
  ε / 16 < T ∨ ε ^ 2 * T ^ 2 * (X * Real.sqrt X) < 46000 * H ∨
    (H / (128 * X) < T ∧ T ≤ 17 * H / X) ∨ H ^ 2 < 64 * X

/-- The possible bad cells of band `i`. -/
def Kbad (H ε : ℝ) (i : ℕ) : Finset ℕ :=
  (Finset.range (⌈π / (2 * Tc H (2 ^ i))⌉₊ + 1)).filter fun k =>
    Tc H (2 ^ i) * 2 ^ k ≤ π / 2 ∧ BadCell H ε (2 ^ i) (Tc H (2 ^ i) * 2 ^ k)

theorem W_ne_zero_nonempty {H n t : ℝ} (h : W H n t ≠ 0) : (E H n t).Nonempty := by
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  exact h (by rw [W, he]; simp)

/-- Angle bound from a nonempty trace set, for `X ≥ H`. -/
theorem τmin_of_nonempty {H X n t : ℝ} (hH : 3 ≤ H) (hXH : H ≤ X) (hXn : X ≤ n)
    (hn : n ≤ 2 * H ^ 2) (hE : (E H n t).Nonempty) : τmin t ≤ 17 * H / X := by
  have hc := Cubic.BoxAsymptotic.Bands.cos_of_nonempty hH hXH hXn hn hE
  have hl := one_sub_abs_cos_ge t
  have hX : 0 < X := by linarith
  have hpi0 : 0 < π := Real.pi_pos
  have h0 : 0 ≤ τmin t := le_min (abs_nonneg _) (abs_nonneg _)
  have : τmin t ^ 2 ≤ (17 * H / X) ^ 2 := by
    have h1 : 2 * τmin t ^ 2 / π ^ 2 ≤ 54 * H ^ 2 / X ^ 2 := hl.trans hc
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
    rw [div_pow]
    rw [le_div_iff₀ (by positivity)]
    have hpi := Cubic.BoxAsymptotic.BulkW.pi_sq_lt
    nlinarith
  exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this


/-- A non-core, non-critical pair with `W ≠ 0` lies in a bad cell. -/
theorem cell_bad {H ε : ℝ} (hH : 3 ≤ H) {x : ℕ × (ℤ × ℤ)} (hx : x ∈ Bset H) (hn4 : 4 ≤ x.1)
    (hcore : ¬ ∃ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = π) ∧ InCore H ε x.1 (τof θ₀ (θ x.2)))
    (hW : W H x.1 (θ x.2) ≠ 0) (hT : Tc H (2 ^ band x) < τmin (θ x.2)) :
    cellIdx H x ∈ Kbad H ε (band x) := by
  have hH0 : 0 < H := by linarith
  obtain ⟨h1, hN, -⟩ := mem_Bset.mp (by simpa using hx : (x.1, x.2) ∈ Bset H)
  set X : ℝ := 2 ^ band x
  have hX0 : 0 < X := by positivity
  have hbb := band_bounds h1
  have hXn : X ≤ x.1 := hbb.1
  have hn2X : (x.1 : ℝ) ≤ 2 * X := by rw [pow_succ] at hbb; linarith [hbb.2]
  have hnH : (x.1 : ℝ) ≤ 2 * H ^ 2 :=
    (by exact_mod_cast hN : (x.1 : ℝ) ≤ Nmax H).trans (Cubic.BoxAsymptotic.Bands.Nmax_le hH)
  set T := Tc H X
  have hT0 : 0 < T := Tc_pos hH0 hX0
  set k := cellIdx H x
  obtain ⟨hk1, hk2⟩ := cellIdx_spec hH0 hT
  set τ := τmin (θ x.2)
  have hτπ := τmin_le (θ x.2)
  have hTk : T * 2 ^ k ≤ π / 2 := hk1.trans hτπ
  rw [Kbad, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hTk, ?_⟩
  · -- `k < ⌈π/(2T)⌉₊ + 1`
    have h2k : (2 : ℝ) ^ k ≤ π / (2 * T) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have : (k : ℝ) ≤ π / (2 * T) :=
      (by exact_mod_cast (Nat.lt_two_pow_self).le : ((k : ℕ) : ℝ) ≤ 2 ^ k).trans h2k
    have := this.trans (Nat.le_ceil _)
    have : k ≤ ⌈π / (2 * T)⌉₊ := by exact_mod_cast this
    exact Nat.lt_succ_of_le this
  · -- badness
    by_contra hgood
    simp only [BadCell, not_or, not_lt, not_and, not_le] at hgood
    obtain ⟨g1, g2, g3, g4⟩ := hgood
    -- the nearer centre
    have hnear : ∃ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = π) ∧ τof θ₀ (θ x.2) = τ := by
      simp only [τ, τmin]
      rcases le_total (τof 0 (θ x.2)) (τof π (θ x.2)) with hl | hl
      · exact ⟨0, Or.inl rfl, (min_eq_left hl).symm⟩
      · exact ⟨π, Or.inr rfl, (min_eq_right hl).symm⟩
    obtain ⟨θ₀, hθ₀, hτeq⟩ := hnear
    apply hcore
    refine ⟨θ₀, hθ₀, ?_⟩
    rw [hτeq]
    have hτ0 : 0 < τ := lt_trans hT0 hT
    have hTkH : T * 2 ^ k ≤ H / (128 * X) := by
      by_contra hlt; push_neg at hlt
      have h17 := g3 hlt
      rcases le_or_gt H X with hXH | hXH
      · have := τmin_of_nonempty hH hXH hXn hnH (W_ne_zero_nonempty hW)
        linarith
      · have : π / 2 < 17 * H / X := by
          rw [lt_div_iff₀ hX0]; nlinarith [Real.pi_lt_d2]
        linarith
    refine ⟨by exact_mod_cast hn4, hτ0, by linarith, ?_, ?_, by linarith⟩
    · -- `46000 H ≤ ε² τ² n √n`
      have hsq : Real.sqrt X ≤ Real.sqrt x.1 := Real.sqrt_le_sqrt hXn
      have hτ2 : (T * 2 ^ k) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by positivity) hk1 2
      have hXX : X * Real.sqrt X ≤ x.1 * Real.sqrt x.1 :=
        mul_le_mul hXn hsq (Real.sqrt_nonneg _) (by positivity)
      calc 46000 * H ≤ ε ^ 2 * (T * 2 ^ k) ^ 2 * (X * Real.sqrt X) := g2
        _ ≤ ε ^ 2 * τ ^ 2 * (x.1 * Real.sqrt x.1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hτ2 (by positivity)) hXX (by positivity)
            (by positivity)
    · -- `n τ ≤ H/32`
      have : (x.1 : ℝ) * τ ≤ 2 * X * (2 * (T * 2 ^ k)) :=
        mul_le_mul hn2X hk2 hτ0.le (by positivity)
      have : 2 * X * (2 * (T * 2 ^ k)) ≤ 2 * X * (2 * (H / (128 * X))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : 2 * X * (2 * (H / (128 * X))) = H / 32 := by field_simp; ring
      linarith


theorem logb_le_of_le {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) : logb 2 y ≤ logb 2 z :=
  (logb_le_logb (by norm_num) hy (by linarith)).mpr hyz

theorem logb_div_eps {a ε : ℝ} (ha : 0 < a) (hε0 : 0 < ε) :
    logb 2 (a / ε) = logb 2 a + logb 2 (1 / ε) := by
  rw [div_eq_mul_one_div a ε, logb_mul ha.ne' (by positivity)]

theorem logb_le_pow {a : ℝ} (ha : 0 < a) {m : ℕ} (h : a ≤ 2 ^ m) : logb 2 a ≤ m := by
  have := logb_le_of_le ha h
  rwa [Cubic.BoxAsymptotic.GoodCount.logb_two_pow] at this

/-- **Bad cells per band.** -/
theorem card_Kbad {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) (i : ℕ)
    (hX : (2 : ℝ) ^ i ≤ 2 * H ^ 2) :
    ((Kbad H ε i).card : ℝ) ≤ 2 * logb 2 (1 / ε) + 25 +
      (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0) := by
  have hH0 : 0 < H := by linarith
  set X : ℝ := 2 ^ i
  have hX0 : 0 < X := by positivity
  set T := Tc H X
  have hT0 : 0 < T := Tc_pos hH0 hX0
  have he := Cubic.BoxAsymptotic.GoodCount.e_nonneg hε0 hε1
  have hmem : ∀ k ∈ Kbad H ε i, T * 2 ^ k ≤ π / 2 ∧ BadCell H ε X (T * 2 ^ k) := fun k hk =>
    (Finset.mem_filter.mp hk).2
  have hTle : ∀ k : ℕ, T ≤ T * 2 ^ k := fun k =>
    le_mul_of_one_le_right hT0.le (one_le_pow₀ (by norm_num))
  split_ifs with hbig
  · -- a top band: all cells
    have hc := count_range hT0 (Kbad H ε i) fun k hk => ⟨hTle k, (hmem k hk).1⟩
    have hTH : π / 2 / T ≤ H := by
      rw [div_le_iff₀ hT0]
      have hsq := Tc_sq hH0 hX0
      have hsX : Real.sqrt X ≤ 2 * H := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have hXX : X * Real.sqrt X ≤ 4 * H ^ 3 := by
        have := mul_le_mul hX hsX (Real.sqrt_nonneg _) (by positivity)
        nlinarith
      -- `T² ≥ 134 H/(4H³) ≥ (π/(2H))²`
      have hT2 : (π / (2 * H)) ^ 2 ≤ T ^ 2 := by
        have h1 : T ^ 2 * (4 * H ^ 3) ≥ 134 * H := by
          calc T ^ 2 * (4 * H ^ 3) ≥ T ^ 2 * (X * Real.sqrt X) :=
                mul_le_mul_of_nonneg_left hXX (sq_nonneg _)
            _ = 134 * H := hsq
        rw [div_pow, div_le_iff₀ (by positivity)]
        have hpi := Cubic.BoxAsymptotic.BulkW.pi_sq_lt
        nlinarith
      have := (pow_le_pow_iff_left₀ (by positivity) hT0.le (by norm_num)).mp hT2
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hlog : logb 2 (π / 2 / T) ≤ logb 2 H := logb_le_of_le (by positivity) hTH
    have hlH : 0 ≤ logb 2 H := logb_nonneg (by norm_num) (by linarith)
    have : max 0 (logb 2 (π / 2 / T)) ≤ logb 2 H := max_le hlH hlog
    linarith
  · -- the other bands: three dyadic ranges
    push_neg at hbig
    set F1 := (Kbad H ε i).filter fun k => ε / 16 < T * 2 ^ k
    set F2 := (Kbad H ε i).filter fun k => ε ^ 2 * (T * 2 ^ k) ^ 2 * (X * Real.sqrt X) < 46000 * H
    set F3 := (Kbad H ε i).filter fun k => H / (128 * X) < T * 2 ^ k ∧ T * 2 ^ k ≤ 17 * H / X
    have hsub : Kbad H ε i ⊆ F1 ∪ (F2 ∪ F3) := by
      intro k hk
      obtain ⟨-, hb⟩ := hmem k hk
      rcases hb with h | h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, h⟩))
      · exact absurd h (not_lt.mpr hbig)
    have c1 := count_range (A := ε / 16) (B := π / 2) (by positivity) F1 fun k hk =>
      ⟨(Finset.mem_filter.mp hk).2.le, (hmem k (Finset.mem_filter.mp hk).1).1⟩
    have hB2 : ∀ k ∈ F2, T * 2 ^ k ≤ 32 * T / ε := by
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      have hsq := Tc_sq hH0 hX0
      have hXX : 0 < X * Real.sqrt X := by positivity
      -- `(T 2^k)² < 46000 H/(ε² X√X) ≤ (32 T/ε)²`
      have : (T * 2 ^ k) ^ 2 ≤ (32 * T / ε) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]
        have : ε ^ 2 * (T * 2 ^ k) ^ 2 * (X * Real.sqrt X) ≤ 1024 * T ^ 2 * (X * Real.sqrt X) := by
          nlinarith
        have := le_of_mul_le_mul_right (by linarith : (T * 2 ^ k) ^ 2 * ε ^ 2 * (X * Real.sqrt X) ≤
          (32 * T) ^ 2 * (X * Real.sqrt X)) hXX
        exact this
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
    have c2 := count_range (A := T) (B := 32 * T / ε) hT0 F2 fun k hk => ⟨hTle k, hB2 k hk⟩
    have c3 := count_range (A := H / (128 * X)) (B := 17 * H / X) (by positivity) F3
      fun k hk => ⟨(Finset.mem_filter.mp hk).2.1.le, (Finset.mem_filter.mp hk).2.2⟩
    -- the logarithms
    have l1 : max 0 (logb 2 (π / 2 / (ε / 16))) ≤ 5 + logb 2 (1 / ε) := by
      apply max_le (by linarith)
      rw [show π / 2 / (ε / 16) = 8 * π / ε by field_simp; ring, logb_div_eps (by positivity) hε0]
      have := logb_le_pow (by positivity : (0 : ℝ) < 8 * π) (m := 5)
        (by norm_num; nlinarith [Real.pi_lt_d2])
      push_cast at this; linarith
    have l2 : max 0 (logb 2 (32 * T / ε / T)) ≤ 5 + logb 2 (1 / ε) := by
      apply max_le (by linarith)
      rw [show 32 * T / ε / T = 32 / ε by field_simp, logb_div_eps (by norm_num) hε0,
        show (32 : ℝ) = 2 ^ 5 by norm_num, Cubic.BoxAsymptotic.GoodCount.logb_two_pow]
      push_cast; linarith
    have l3 : max 0 (logb 2 (17 * H / X / (H / (128 * X)))) ≤ 12 := by
      apply max_le (by norm_num)
      rw [show 17 * H / X / (H / (128 * X)) = 2176 by field_simp; ring]
      have := logb_le_pow (by norm_num : (0 : ℝ) < 2176) (m := 12) (by norm_num)
      push_cast at this; linarith
    have a1 := Finset.card_le_card hsub
    have a2 := Finset.card_union_le F1 (F2 ∪ F3)
    have a3 := Finset.card_union_le F2 F3
    have hc : (Kbad H ε i).card ≤ F1.card + (F2.card + F3.card) := by omega
    have : ((Kbad H ε i).card : ℝ) ≤ F1.card + (F2.card + F3.card) := by exact_mod_cast hc
    linarith


/-- The critical term of a band: `(T_c X + √X) √(54H/√X) = √7236 H + √(54 H √X)`. -/
theorem crit_eval {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (Tc H X * X + Real.sqrt X) * Real.sqrt (54 * H / Real.sqrt X) =
      Real.sqrt 7236 * H + Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt X) := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have e1 : Tc H X * X * Real.sqrt (54 * H / Real.sqrt X) = Real.sqrt 7236 * H := by
    have hT := Tc_pos hH hX
    refine (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : 2 ≠ 0)).mp ?_
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    simp only [Tc]
    rw [Real.sq_sqrt (by positivity)]
    have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
    field_simp
    rw [sq, hss]; ring
  have e2 : Real.sqrt X * Real.sqrt (54 * H / Real.sqrt X) =
      Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt X) := by
    rw [← Real.sqrt_mul hX.le, show X * (54 * H / Real.sqrt X) = 54 * H * (X / Real.sqrt X) by ring,
      Real.div_sqrt, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  rw [add_mul, e1, e2]

/-- The cell term: `(2 T_k X + √X) · 500 H/(X T_k) = 1000 H + 500 H/(√X T_k)`. -/
theorem cell_eval {H X T : ℝ} (hX : 0 < X) (hT : 0 < T) :
    (2 * T * X + Real.sqrt X) * (500 * H / (X * T)) = 1000 * H + 500 * H / (Real.sqrt X * T) := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have : Real.sqrt X / X = 1 / Real.sqrt X := by
    rw [div_eq_div_iff hX.ne' hsX.ne', one_mul, Real.mul_self_sqrt hX.le]
  field_simp
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
  linear_combination (500 * H) * hss

theorem cell_tail {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    H / (Real.sqrt X * Tc H X) = Real.sqrt H * Real.sqrt (Real.sqrt X) / Real.sqrt 134 := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hT := Tc_pos hH hX
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hsq := Tc_sq hH hX
  -- square both sides
  have h1 : 0 ≤ H * Real.sqrt 134 := by positivity
  have h2 : 0 ≤ Real.sqrt H * Real.sqrt (Real.sqrt X) * (Real.sqrt X * Tc H X) := by positivity
  refine (pow_left_inj₀ h1 h2 (by norm_num : 2 ≠ 0)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num), mul_pow, mul_pow, mul_pow, Real.sq_sqrt hH.le,
    Real.sq_sqrt hsX.le, Real.sq_sqrt hX.le]
  have e : Real.sqrt X * (X * Tc H X ^ 2) = Tc H X ^ 2 * (X * Real.sqrt X) := by ring
  rw [mul_assoc H, e, hsq]; ring


theorem geom_half (S : Finset ℕ) : ∑ k ∈ S, ((1 : ℝ) / 2) ^ k ≤ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsub : S ⊆ Finset.range (S.max' hne + 1) := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' k hk))
  calc ∑ k ∈ S, ((1 : ℝ) / 2) ^ k ≤ ∑ k ∈ Finset.range (S.max' hne + 1), ((1 : ℝ) / 2) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 := by
        rw [geom_sum_eq (by norm_num)]
        have : 0 < ((1 : ℝ) / 2) ^ (S.max' hne + 1) := by positivity
        rw [div_le_iff_of_neg (by norm_num)]; linarith

/-- **One band of the discarded region.** -/
theorem band_total {Ks : ℝ} (hKs : 0 < Ks)
    (hsec : ∀ (H X θ₀ Θ : ℝ), 2 ≤ X → 0 ≤ Θ → ∀ F : Finset (ℕ × (ℤ × ℤ)), F ⊆ Bset H →
      (∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧
        Cubic.BoxAsymptotic.AngularSpacing.near (θ x.2) θ₀ Θ) →
      (F.card : ℝ) ≤ Ks * (Θ * X + Real.sqrt X) * Real.log X)
    {H ε : ℝ} (hH : 3 ≤ H) {i : ℕ} (hi : 1 ≤ i) (F : Finset (ℕ × (ℤ × ℤ))) (hF : F ⊆ Bset H)
    (hb : ∀ x ∈ F, band x = i)
    (hbad : ∀ x ∈ F, 4 ≤ x.1 ∧
      (¬ ∃ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = π) ∧ InCore H ε x.1 (τof θ₀ (θ x.2))) ∧
      W H x.1 (θ x.2) ≠ 0) :
    ∑ x ∈ F, W H x.1 (θ x.2) ≤ Ks * Real.log (2 ^ i) *
      (8 * Real.sqrt 7236 * H + 8 * Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt (2 ^ i)) +
        2000 * H * (Kbad H ε i).card +
        2000 * (Real.sqrt H * Real.sqrt (Real.sqrt (2 ^ i)) / Real.sqrt 134)) := by
  have hH0 : 0 < H := by linarith
  set X : ℝ := 2 ^ i
  have hX0 : 0 < X := by positivity
  have hX2 : 2 ≤ X := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
    simpa [X] using this
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set T := Tc H X
  have hT0 : 0 < T := Tc_pos hH0 hX0
  have hbd := band_bound hsec hH hi F hF hb
  -- the cells occurring are bad
  have himg : (F.filter fun x => T < τmin (θ x.2)).image (cellIdx H) ⊆ Kbad H ε i := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hxF, hTx⟩ := Finset.mem_filter.mp hx
    obtain ⟨h4, hc, hW⟩ := hbad x hxF
    have hbx := hb x hxF
    have := cell_bad hH (hF hxF) h4 hc hW (by rw [hbx]; exact hTx)
    rwa [hbx] at this
  have hcellnn : ∀ k : ℕ, 0 ≤ 2 * (Ks * (2 * (T * 2 ^ k) * X + Real.sqrt X) * Real.log X) *
      (500 * H / (X * (T * 2 ^ k))) := fun k => by positivity
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg himg (fun k _ _ => hcellnn k)
  -- evaluate
  have hcrit : 2 * (Ks * (T * X + Real.sqrt X) * Real.log X) *
      (4 * Real.sqrt (54 * H / Real.sqrt X)) = 8 * Ks * Real.log X *
        (Real.sqrt 7236 * H + Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt X)) := by
    rw [← crit_eval hH0 hX0]; ring
  have hcell : ∀ k : ℕ, 2 * (Ks * (2 * (T * 2 ^ k) * X + Real.sqrt X) * Real.log X) *
      (500 * H / (X * (T * 2 ^ k))) = 2 * Ks * Real.log X *
        (1000 * H + 500 * (H / (Real.sqrt X * T)) * ((1 : ℝ) / 2) ^ k) := fun k => by
    have := cell_eval (H := H) hX0 (by positivity : 0 < T * 2 ^ k)
    rw [show 2 * (Ks * (2 * (T * 2 ^ k) * X + Real.sqrt X) * Real.log X) *
      (500 * H / (X * (T * 2 ^ k))) = 2 * Ks * Real.log X * ((2 * (T * 2 ^ k) * X +
        Real.sqrt X) * (500 * H / (X * (T * 2 ^ k)))) by ring, this]
    congr 2
    rw [one_div_pow]; field_simp
  have hK : ∑ k ∈ Kbad H ε i, 2 * (Ks * (2 * (T * 2 ^ k) * X + Real.sqrt X) * Real.log X) *
      (500 * H / (X * (T * 2 ^ k))) ≤ 2 * Ks * Real.log X *
        (1000 * H * (Kbad H ε i).card + 1000 * (H / (Real.sqrt X * T))) := by
    simp_rw [hcell]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have := geom_half (Kbad H ε i)
    have hpos : 0 ≤ 500 * (H / (Real.sqrt X * T)) := by positivity
    have := mul_le_mul_of_nonneg_left this hpos
    linarith
  have htail := cell_tail hH0 hX0
  rw [hcrit] at hbd
  calc ∑ x ∈ F, W H x.1 (θ x.2)
      ≤ 8 * Ks * Real.log X * (Real.sqrt 7236 * H + Real.sqrt 54 * Real.sqrt H *
          Real.sqrt (Real.sqrt X)) + 2 * Ks * Real.log X *
          (1000 * H * (Kbad H ε i).card + 1000 * (H / (Real.sqrt X * T))) := by linarith
    _ = _ := by rw [htail]; ring


open Cubic.BoxAsymptotic.BulkSum (wb)
open Cubic.BoxAsymptotic.GoodSet (Imax)

/-- At most `8` bands have `H²/64 < 2^i ≤ 2H²`. -/
theorem card_top {H : ℝ} (hH : 3 ≤ H) (S : Finset ℕ)
    (hS : ∀ i ∈ S, H ^ 2 < 64 * (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ 2 * H ^ 2) : (S.card : ℝ) ≤ 8 := by
  have hc := count_range (A := H ^ 2 / 64) (B := 2 * H ^ 2) (c := 1) (by positivity) S
    fun i hi => ⟨by rw [one_mul]; linarith [(hS i hi).1], by rw [one_mul]; exact (hS i hi).2⟩
  have : 2 * H ^ 2 / (H ^ 2 / 64) = 2 ^ 7 := by field_simp; norm_num
  rw [this, Cubic.BoxAsymptotic.GoodCount.logb_two_pow] at hc
  push_cast at hc
  linarith [max_eq_right (by norm_num : (0 : ℝ) ≤ 7)]

theorem qpow_le {H : ℝ} (hH : 3 ≤ H) {i : ℕ} (hi : (2 : ℝ) ^ i ≤ 2 * H ^ 2) :
    Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) ≤ 2 * Real.sqrt H := by
  have h1 : Real.sqrt ((2 : ℝ) ^ i) ≤ 2 * H := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  calc Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) ≤ Real.sqrt (2 * H) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt 2 * Real.sqrt H := Real.sqrt_mul (by norm_num) _
    _ ≤ 2 * Real.sqrt H := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_left (by norm_num)]; norm_num


/-- Not in the core. -/
def Bad (H ε : ℝ) (x : ℕ × (ℤ × ℤ)) : Prop :=
  ¬ ∃ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = π) ∧ InCore H ε x.1 (τof θ₀ (θ x.2))

theorem term_le {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    {x : ℕ × (ℤ × ℤ)} (hx : x ∈ Bset H) :
    W H x.1 (θ x.2) * (1 - (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2))) ≤
      if Bad H ε x ∧ W H x.1 (θ x.2) ≠ 0 then W H x.1 (θ x.2) else 0 := by
  have h1 := (mem_Bset.mp (by simpa using hx : (x.1, x.2) ∈ Bset H)).1
  have hn : (0 : ℝ) < x.1 := by exact_mod_cast h1
  obtain ⟨w0, w1⟩ := Cubic.BoxAsymptotic.Core.wb_total_le (H := H) (ε := ε) (t := θ x.2) hn
  have hW := W_nonneg H x.1 (θ x.2)
  split_ifs with h
  · have := mul_le_mul_of_nonneg_left (by linarith : 1 - (wb H ε 0 x.1 (θ x.2) +
      wb H ε π x.1 (θ x.2)) ≤ 1) hW
    linarith
  · rw [not_and_or] at h
    rcases h with h | h
    · simp only [Bad, not_not] at h
      obtain ⟨θ₀, hθ₀, hc⟩ := h
      rw [Cubic.BoxAsymptotic.Core.wb_total_eq_one hH hε0 hε1 hθ₀ hc]; simp
    · rw [not_not] at h; rw [h, zero_mul]


/-- The small pairs `n ≤ 3` carry `≤ 27 K₀ · 4 √(54 H)`. -/
theorem small_sum {K₀ : ℝ} (hball : ∀ R : ℝ, 0 ≤ R →
      ((Cubic.BoxAsymptotic.LatticeSums.ball R).card : ℝ) ≤ K₀ * R)
    {H : ℝ} (hH : 0 ≤ H) (S : Finset (ℕ × (ℤ × ℤ))) (hS : S ⊆ Bset H)
    (h3 : ∀ x ∈ S, x.1 ≤ 3) :
    ∑ x ∈ S, W H x.1 (θ x.2) ≤ K₀ * 27 * (4 * Real.sqrt (54 * H)) := by
  have hinj : Set.InjOn Prod.snd (S : Set (ℕ × (ℤ × ℤ))) := by
    intro x hx y hy h
    have hx' := (mem_Bset.mp (by simpa using hS hx : (x.1, x.2) ∈ Bset H)).2.2
    have hy' := (mem_Bset.mp (by simpa using hS hy : (y.1, y.2) ∈ Bset H)).2.2
    rw [h] at hx'
    exact Prod.ext (Cubic.BoxAsymptotic.Bands.n_unique hx' hy') h
  have hcard : (S.card : ℝ) ≤ K₀ * 27 := by
    refine le_trans ?_ (hball 27 (by norm_num))
    rw [← Finset.card_image_of_injOn hinj]
    refine Nat.cast_le.mpr (Finset.card_le_card fun β hβ => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hn1, -, hadm⟩ := mem_Bset.mp (by simpa using hS hx : (x.1, x.2) ∈ Bset H)
    have hN : Cubic.BoxAsymptotic.EisensteinCoordinates.nrm x.2 = (x.1 : ℤ) ^ 3 := hadm.1
    rw [Cubic.BoxAsymptotic.LatticeSums.mem_ball]
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0] at hN
      have : (x.1 : ℤ) ^ 3 = 0 := by rw [← hN]; simp [Cubic.BoxAsymptotic.EisensteinCoordinates.nrm]
      have : (x.1 : ℤ) = 0 := pow_eq_zero_iff (by norm_num) |>.mp this
      omega
    · rw [hN]; push_cast
      have : (x.1 : ℝ) ≤ 3 := by exact_mod_cast h3 x hx
      have h0 : (0 : ℝ) ≤ x.1 := Nat.cast_nonneg _
      have := pow_le_pow_left₀ h0 this 3
      norm_num at this; linarith
  have hW : ∀ x ∈ S, W H x.1 (θ x.2) ≤ 4 * Real.sqrt (54 * H) := by
    intro x hx
    have hn1 := (mem_Bset.mp (by simpa using hS hx : (x.1, x.2) ∈ Bset H)).1
    have hn : (1 : ℝ) ≤ x.1 := by exact_mod_cast hn1
    refine (W_le_sqrt (by linarith)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact div_le_self (by positivity) (Real.one_le_sqrt.mpr hn)
  calc ∑ x ∈ S, W H x.1 (θ x.2) ≤ ∑ _x ∈ S, 4 * Real.sqrt (54 * H) := Finset.sum_le_sum hW
    _ = S.card * (4 * Real.sqrt (54 * H)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K₀ * 27 * (4 * Real.sqrt (54 * H)) := mul_le_mul_of_nonneg_right hcard (by positivity)


theorem aux_le {H L e : ℝ} (hH : 0 ≤ H) (hL : 1 ≤ L) (he : 0 ≤ e) :
    H ≤ H * L ^ 2 * (1 + e) ∧ H * L ≤ H * L ^ 2 * (1 + e) := by
  have h1 : 1 ≤ L ^ 2 := by nlinarith
  have h2 : L ≤ L ^ 2 := by nlinarith
  have h3 : L ^ 2 ≤ L ^ 2 * (1 + e) := le_mul_of_one_le_right (by positivity) (by linarith)
  constructor
  · calc H = H * 1 := by ring
      _ ≤ H * (L ^ 2 * (1 + e)) := mul_le_mul_of_nonneg_left (by linarith) hH
      _ = _ := by ring
  · calc H * L ≤ H * (L ^ 2 * (1 + e)) := mul_le_mul_of_nonneg_left (by linarith) hH
      _ = _ := by ring

/-- **The discarded region**: `Σ W (1 - w_bulk) ≤ K H (log H)² (1 + log₂(1/ε))`. -/
theorem discard : ∃ K : ℝ, 0 < K ∧ ∀ H ε : ℝ, 3 ≤ H → 0 < ε → ε ≤ 1 / 10 →
    ∑ x ∈ Bset H, W H x.1 (θ x.2) * (1 - (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2))) ≤
      K * H * Real.log H ^ 2 * (1 + logb 2 (1 / ε)) := by
  obtain ⟨Ks, hKs, hsec⟩ := Cubic.BoxAsymptotic.Bands.sector
  obtain ⟨K₀, hK₀, hball⟩ := Cubic.BoxAsymptotic.LatticeSums.card_ball
  obtain ⟨K₂, hK₂, hreal⟩ := Cubic.BoxAsymptotic.Bands.sum_real
  refine ⟨900 * K₀ + K₂ + 2000000 * Ks, by positivity, fun H ε hH hε0 hε1 => ?_⟩
  have hH0 : 0 < H := by linarith
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  set L := Real.log H
  set e := logb 2 (1 / ε)
  have he := Cubic.BoxAsymptotic.GoodCount.e_nonneg hε0 hε1
  set Sbad := (Bset H).filter fun x => Bad H ε x ∧ W H x.1 (θ x.2) ≠ 0
  -- termwise
  have hstep1 : ∑ x ∈ Bset H, W H x.1 (θ x.2) *
      (1 - (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2))) ≤ ∑ x ∈ Sbad, W H x.1 (θ x.2) := by
    refine (Finset.sum_le_sum fun x hx => term_le hH hε0 hε1 hx).trans (le_of_eq ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine hstep1.trans ?_
  -- split `Sbad`
  set S₁ := Sbad.filter fun x => x.1 ≤ 3
  set S₂ := (Sbad.filter fun x => ¬ x.1 ≤ 3).filter fun x => x.2.2 = 0
  set S₃ := (Sbad.filter fun x => ¬ x.1 ≤ 3).filter fun x => ¬ x.2.2 = 0
  have hsplit : ∑ x ∈ Sbad, W H x.1 (θ x.2) = ∑ x ∈ S₁, W H x.1 (θ x.2) +
      (∑ x ∈ S₂, W H x.1 (θ x.2) + ∑ x ∈ S₃, W H x.1 (θ x.2)) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hSbad : Sbad ⊆ Bset H := Finset.filter_subset _ _
  -- `S₁`
  have h1 := small_sum hball hH0.le S₁ (fun x hx => hSbad (Finset.mem_filter.mp hx).1)
    fun x hx => (Finset.mem_filter.mp hx).2
  have h1' : K₀ * 27 * (4 * Real.sqrt (54 * H)) ≤ 864 * K₀ * H := by
    have hs : Real.sqrt (54 * H) ≤ 8 * H := by
      rw [Real.sqrt_mul (by norm_num)]
      have h54 : Real.sqrt 54 ≤ 8 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hsH : Real.sqrt H ≤ H := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
      exact mul_le_mul h54 hsH (Real.sqrt_nonneg _) (by norm_num)
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ K₀ * 27 * 4)
    linarith
  -- `S₂`
  have h2 : ∑ x ∈ S₂, W H x.1 (θ x.2) ≤ K₂ * H * L := by
    refine le_trans ?_ (hreal H hH)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => W_nonneg _ _ _
    obtain ⟨hx1, hB⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hSbad (Finset.mem_filter.mp hx1).1, hB⟩
  -- `S₃` by bands
  set I := Imax H
  have hmaps : ∀ x ∈ S₃, band x ∈ Finset.Icc 1 I := by
    intro x hx
    obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx2, h4⟩ := Finset.mem_filter.mp hx1
    have hb := Cubic.BoxAsymptotic.Bands.mem_bands (hSbad hx2)
    rw [Finset.mem_range] at hb
    refine Finset.mem_Icc.mpr ⟨?_, by simp only [I, Imax]; omega⟩
    have h4' : 2 ^ 2 ≤ x.1 := by omega
    have := Nat.log_mono_right (b := 2) h4'
    rw [Nat.log_pow (by norm_num)] at this
    simp only [band]; omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := band) (t := Finset.Icc 1 I) hmaps]
  have hband : ∀ i ∈ Finset.Icc 1 I, ∑ x ∈ S₃.filter (fun x => band x = i), W H x.1 (θ x.2) ≤
      Ks * (3 * L) * H * (52000 + 4000 * e +
        2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) := by
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hXH : (2 : ℝ) ^ i ≤ 2 * H ^ 2 := by
      have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Finset.mem_Icc.mp hi).2
      have h' : ((2 ^ i : ℕ) : ℝ) ≤ 2 ^ I := by exact_mod_cast hp
      have hN := Nat.pow_log_le_self 2 (show Nmax H ≠ 0 by
        have : 1 ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
        omega)
      have h'' : ((2 ^ I : ℕ) : ℝ) ≤ Nmax H := by exact_mod_cast hN
      push_cast at h' h''
      exact h'.trans (h''.trans (Cubic.BoxAsymptotic.Bands.Nmax_le hH))
    have hbt := band_total hKs hsec hH hi1 (S₃.filter fun x => band x = i)
      (fun x hx => hSbad (Finset.mem_filter.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hx).1).1).1)
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => by
        obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx2, -⟩ := Finset.mem_filter.mp hx1
        obtain ⟨hx3, h4⟩ := Finset.mem_filter.mp hx2
        obtain ⟨-, hb, hW⟩ := Finset.mem_filter.mp hx3
        exact ⟨by omega, hb, hW⟩)
    refine hbt.trans ?_
    have hlog : Real.log ((2 : ℝ) ^ i) ≤ 3 * L :=
      Cubic.BoxAsymptotic.Bands.log_le hH (one_le_pow₀ (by norm_num)) hXH
    have hlog0 : 0 ≤ Real.log ((2 : ℝ) ^ i) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    have hq := qpow_le hH hXH
    have hK := card_Kbad hH hε0 hε1 i hXH
    have hsH : Real.sqrt H * Real.sqrt H = H := Real.mul_self_sqrt hH0.le
    have hq' : Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) ≤ 2 * H := by
      have := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg H); nlinarith
    have h7236 : Real.sqrt 7236 ≤ 86 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h54 : Real.sqrt 54 ≤ 8 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h134 : (11 : ℝ) ≤ Real.sqrt 134 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hinner : 8 * Real.sqrt 7236 * H + 8 * Real.sqrt 54 * Real.sqrt H *
        Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) + 2000 * H * (Kbad H ε i).card +
        2000 * (Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) / Real.sqrt 134) ≤
        H * (52000 + 4000 * e + 2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) := by
      have a1 : 8 * Real.sqrt 7236 * H ≤ 688 * H :=
        mul_le_mul_of_nonneg_right (by linarith) hH0.le
      have a2 : 8 * Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) ≤ 128 * H := by
        have := mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt 54)
        have h2 : 8 * Real.sqrt 54 * (2 * H) ≤ 8 * 8 * (2 * H) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have e : 8 * Real.sqrt 54 * Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) =
            8 * Real.sqrt 54 * (Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i))) := by ring
        linarith
      have a3 : 2000 * (Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) / Real.sqrt 134) ≤
          400 * H := by
        have : Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) / Real.sqrt 134 ≤ 2 * H / 11 :=
          div_le_div₀ (by linarith) hq' (by norm_num) h134
        linarith
      have a4 : 2000 * H * (Kbad H ε i).card ≤ 2000 * H * (2 * e + 25 +
          (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      have e : H * (52000 + 4000 * e + 2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) =
          2000 * H * (2 * e + 25 + (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) +
            2000 * H := by ring
      rw [e]; linarith
    calc Ks * Real.log ((2 : ℝ) ^ i) * (8 * Real.sqrt 7236 * H + 8 * Real.sqrt 54 * Real.sqrt H *
          Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) + 2000 * H * (Kbad H ε i).card +
          2000 * (Real.sqrt H * Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) / Real.sqrt 134))
        ≤ Ks * (3 * L) * (H * (52000 + 4000 * e +
            2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hlog hKs.le) hinner (by positivity)
            (by positivity)
      _ = _ := by ring
  -- the band sum
  have hIcard : ((Finset.Icc 1 I).card : ℝ) ≤ 6 * L := by
    rw [Nat.card_Icc]
    have := Cubic.BoxAsymptotic.Bands.card_bands hH
    push_cast at this ⊢; simp only [I, Imax] at this ⊢; linarith
  have htop : ((((Finset.Icc 1 I).filter fun i => H ^ 2 < 64 * (2 : ℝ) ^ i)).card : ℝ) ≤ 8 :=
    card_top hH _ fun i hi => by
      obtain ⟨hi', hlt⟩ := Finset.mem_filter.mp hi
      refine ⟨hlt, ?_⟩
      have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Finset.mem_Icc.mp hi').2
      have h' : ((2 ^ i : ℕ) : ℝ) ≤ 2 ^ I := by exact_mod_cast hp
      have hN := Nat.pow_log_le_self 2 (show Nmax H ≠ 0 by
        have : 1 ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
        omega)
      have h'' : ((2 ^ I : ℕ) : ℝ) ≤ Nmax H := by exact_mod_cast hN
      push_cast at h' h''
      exact h'.trans (h''.trans (Cubic.BoxAsymptotic.Bands.Nmax_le hH))
  have hh : logb 2 H + 1 ≤ 3 * L := by
    have e1 : logb 2 H = L / Real.log 2 := rfl
    have hl2 := Real.log_two_gt_d9
    rw [e1, div_add_one (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hsumi : ∑ i ∈ Finset.Icc 1 I, (52000 + 4000 * e +
      2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) ≤ L * (360000 + 24000 * e) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hA : ((Finset.Icc 1 I).card : ℝ) * (52000 + 4000 * e) ≤ 6 * L * (52000 + 4000 * e) :=
      mul_le_mul_of_nonneg_right hIcard (by positivity)
    have hlH : 0 ≤ logb 2 H := logb_nonneg (by norm_num) (by linarith)
    have hB : ((((Finset.Icc 1 I).filter fun i => H ^ 2 < 64 * (2 : ℝ) ^ i)).card : ℝ) *
        (logb 2 H + 1) ≤ 8 * (3 * L) :=
      mul_le_mul htop hh (by positivity) (by norm_num)
    nlinarith
  have h3 : ∑ i ∈ Finset.Icc 1 I, Ks * (3 * L) * H * (52000 + 4000 * e +
      2000 * (if H ^ 2 < 64 * (2 : ℝ) ^ i then logb 2 H + 1 else 0)) ≤
      Ks * (3 * L) * H * (L * (360000 + 24000 * e)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsumi (by positivity)
  have hfin := add_le_add h1 (add_le_add h2 ((Finset.sum_le_sum hband).trans h3))
  refine hfin.trans ?_
  obtain ⟨q1, q2⟩ := aux_le hH0.le hL he
  have p1 : 864 * K₀ * H ≤ 900 * K₀ * (H * L ^ 2 * (1 + e)) := by
    have a := mul_le_mul_of_nonneg_left q1 (by positivity : (0 : ℝ) ≤ 900 * K₀)
    have b : 864 * K₀ * H ≤ 900 * K₀ * H := by
      have : 0 ≤ K₀ * H := by positivity
      linarith
    linarith
  have p2 : K₂ * H * L ≤ K₂ * (H * L ^ 2 * (1 + e)) := by
    have := mul_le_mul_of_nonneg_left q2 hK₂.le
    linarith
  have p3 : Ks * (3 * L) * H * (L * (360000 + 24000 * e)) ≤
      2000000 * Ks * (H * L ^ 2 * (1 + e)) := by
    have e1 : Ks * (3 * L) * H * (L * (360000 + 24000 * e)) =
        Ks * (H * L ^ 2) * (1080000 + 72000 * e) := by ring
    rw [e1]
    have : 1080000 + 72000 * e ≤ 2000000 * (1 + e) := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Ks * (H * L ^ 2))
    linarith
  have e2 : (900 * K₀ + K₂ + 2000000 * Ks) * H * L ^ 2 * (1 + e) =
      900 * K₀ * (H * L ^ 2 * (1 + e)) + K₂ * (H * L ^ 2 * (1 + e)) +
        2000000 * Ks * (H * L ^ 2 * (1 + e)) := by ring
  rw [e2]
  linarith

end Cubic.BoxAsymptotic.Discard
