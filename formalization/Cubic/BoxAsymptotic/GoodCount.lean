import Cubic.BoxAsymptotic.GoodSet
import Cubic.BoxAsymptotic.DyadicCount
import Cubic.BoxAsymptotic.MainIntegral

/-!
# Counting good pieces at each scale

For `1 ≤ i` with `16·2^i ≤ H²`, `(i, j)` is good iff `A ≤ 2^j ≤ B` with
`A = max(4/ε, 8·2^i/H)` and `B = ε √(2^i √(2^i)) / √(2000 H)`. In base-`2` logarithms,
`log₂ B - log₂ A = g(i) - err` with `g(i) = min(3i/4 - h/2, h/2 - i/4)`, `h = log₂ H`, and
`e + c/2 + 2 ≤ err ≤ 2e + c/2 + 3`, where `e = log₂(1/ε)` and `c = log₂ 2000`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.GoodCount

open Real Cubic.BoxAsymptotic.GoodSet
open Cubic.BoxAsymptotic.Admissible (Nmax)
open Cubic.BoxAsymptotic.BulkW (Good)
open scoped Classical

/-- The lower dyadic bound. -/
def Aq (H ε : ℝ) (i : ℕ) : ℝ := max (4 / ε) (8 * 2 ^ i / H)

/-- The upper dyadic bound. -/
def Bq (H ε : ℝ) (i : ℕ) : ℝ :=
  ε * Real.sqrt ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) / Real.sqrt (2000 * H)

theorem good_iff {H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) {i j : ℕ} (hi : 1 ≤ i)
    (h4 : 16 * (2 : ℝ) ^ i ≤ H ^ 2) :
    Good H ε i j ↔ Aq H ε i ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ Bq H ε i := by
  have hj : (0 : ℝ) < 2 ^ j := by positivity
  have hX : (0 : ℝ) < 2 ^ i := by positivity
  have e1 : ((1 : ℝ) / 2) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
  have hsX : 0 ≤ (2 : ℝ) ^ i * Real.sqrt (2 ^ i) := by positivity
  -- the three conditions
  have c1 : ((1 : ℝ) / 2) ^ j ≤ ε / 4 ↔ 4 / ε ≤ 2 ^ j := by
    rw [e1, div_le_div_iff₀ hj (by norm_num), div_le_iff₀ hε0]; constructor <;> intro h <;> linarith
  have c3 : (2 : ℝ) ^ i * (1 / 2) ^ j ≤ H / 8 ↔ 8 * 2 ^ i / H ≤ 2 ^ j := by
    rw [e1, div_le_iff₀ hH, mul_one_div, div_le_div_iff₀ hj (by norm_num)]
    constructor <;> intro h <;> linarith
  have c2 : 2000 * H ≤ ε ^ 2 * ((1 / 2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) ↔
      (2 : ℝ) ^ j ≤ Bq H ε i := by
    rw [Bq, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)), e1]
    have hr : (2 : ℝ) ^ j * Real.sqrt (2000 * H) = Real.sqrt ((2 ^ j) ^ 2 * (2000 * H)) := by
      symm; rw [Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ j)), Real.sqrt_sq hj.le]
    have hl : ε * Real.sqrt ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) =
        Real.sqrt (ε ^ 2 * ((2 : ℝ) ^ i * Real.sqrt (2 ^ i))) := by
      symm; rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0.le]
    rw [hr, hl, Real.sqrt_le_sqrt_iff (by positivity)]
    have e2 : ε ^ 2 * (1 / (2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) =
        ε ^ 2 * ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) / (2 ^ j) ^ 2 := by field_simp
    rw [e2, le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  constructor
  · intro hg
    exact ⟨max_le (c1.mp hg.g1) (c3.mp hg.g3), c2.mp hg.g2⟩
  · rintro ⟨hA, hB⟩
    have h1 := c1.mpr ((le_max_left _ _).trans hA)
    have h3 := c3.mpr ((le_max_right _ _).trans hA)
    have hj2 : 2 ≤ j := by
      by_contra hlt; push_neg at hlt
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h40 : (40 : ℝ) ≤ 4 / ε := by rw [le_div_iff₀ hε0]; linarith
      have := (le_max_left _ _).trans hA
      linarith
    exact ⟨hi, hj2, h1, c2.mpr hB, h3, h4⟩


theorem logb_max {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logb 2 (max x y) = max (logb 2 x) (logb 2 y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right ((logb_le_logb (by norm_num) hx hy).mpr h)]
  · rw [max_eq_left h, max_eq_left ((logb_le_logb (by norm_num) hy hx).mpr h)]

theorem logb_two_pow (i : ℕ) : logb 2 ((2 : ℝ) ^ i) = i := by
  rw [logb_pow, logb_self_eq_one (by norm_num), mul_one]

theorem logb_sqrt' {x : ℝ} (hx : 0 < x) : logb 2 (Real.sqrt x) = logb 2 x / 2 := by
  rw [Real.sqrt_eq_rpow, logb_rpow_eq_mul_logb_of_pos hx]; ring

theorem logb_A {H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (i : ℕ) :
    logb 2 (Aq H ε i) = max (2 + logb 2 (1 / ε)) (3 + i - logb 2 H) := by
  rw [Aq, logb_max (by positivity) (by positivity)]
  congr 1
  · rw [show 4 / ε = 2 ^ 2 * (1 / ε) by ring, logb_mul (by positivity) (by positivity),
      logb_two_pow]; push_cast; ring
  · rw [logb_div (by positivity) hH.ne', show (8 : ℝ) * 2 ^ i = 2 ^ (i + 3) by ring,
      logb_two_pow]; push_cast; ring

theorem logb_B {H ε : ℝ} (hH : 0 < H) (hε0 : 0 < ε) (i : ℕ) :
    logb 2 (Bq H ε i) =
      -logb 2 (1 / ε) + 3 * i / 4 - logb 2 2000 / 2 - logb 2 H / 2 := by
  have hX : (0 : ℝ) < 2 ^ i := by positivity
  rw [Bq, logb_div (by positivity) (Real.sqrt_pos.mpr (by positivity)).ne',
    logb_mul hε0.ne' (Real.sqrt_pos.mpr (by positivity)).ne',
    logb_sqrt' (by positivity), logb_sqrt' (by positivity),
    logb_mul hX.ne' (Real.sqrt_pos.mpr hX).ne', logb_sqrt' hX, logb_two_pow,
    logb_mul (by norm_num) hH.ne', one_div, logb_inv]
  ring


/-- The number of good `j` at scale `i`. -/
def J (H ε : ℝ) (i : ℕ) : ℕ := ((Finset.Icc 2 (Jmax H)).filter fun j => Good H ε i j).card

theorem sum_G_fst (H ε : ℝ) :
    ∑ p ∈ G H ε, (p.1 : ℝ) = ∑ i ∈ Finset.Icc 1 (Imax H), (i : ℝ) * J H ε i := by
  rw [G, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [J, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The error constant `D = 2e + c/2 + 4`. -/
def D (ε : ℝ) : ℝ := 2 * logb 2 (1 / ε) + logb 2 2000 / 2 + 4

theorem e_nonneg {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) : 0 ≤ logb 2 (1 / ε) :=
  logb_nonneg (by norm_num) (by rw [le_div_iff₀ hε0]; linarith)

/-- **Good pieces per scale**: `|J(i) - max(0, g(i))| ≤ D`. -/
theorem J_bound {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) {i : ℕ} (hi : 1 ≤ i) :
    |(J H ε i : ℝ) - max 0 (MainIntegral.g (logb 2 H) i)| ≤ D ε := by
  have hH0 : 0 < H := by linarith
  set h := logb 2 H
  set e := logb 2 (1 / ε)
  set c := logb 2 2000
  have he := e_nonneg hε0 hε1
  have hc : 0 ≤ c := logb_nonneg (by norm_num) (by norm_num)
  have hg : MainIntegral.g h i = 3 * i / 4 - h / 2 - max 0 (i - h) := by
    simp only [MainIntegral.g]
    rcases le_total (i : ℝ) h with hih | hih
    · rw [max_eq_left (by linarith), min_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring
  rcases le_or_gt (16 * (2 : ℝ) ^ i) (H ^ 2) with h4 | h4
  · -- the dyadic count
    have hA2 : 2 ≤ Aq H ε i := by
      have : (40 : ℝ) ≤ 4 / ε := by rw [le_div_iff₀ hε0]; linarith
      exact le_trans (by linarith) (le_max_left _ _)
    have hB0 : 0 < Bq H ε i := by simp only [Bq]; positivity
    have hBH : Bq H ε i ≤ H := by
      have hX : (0 : ℝ) < 2 ^ i := by positivity
      have hsX : Real.sqrt ((2 : ℝ) ^ i) ≤ H / 4 := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have hXX : (2 : ℝ) ^ i * Real.sqrt (2 ^ i) ≤ H ^ 3 / 64 := by
        have := mul_le_mul (by linarith : (2 : ℝ) ^ i ≤ H ^ 2 / 16) hsX (Real.sqrt_nonneg _)
          (by positivity)
        have e1 : H ^ 2 / 16 * (H / 4) = H ^ 3 / 64 := by ring
        linarith
      simp only [Bq]
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
      have hs1 : Real.sqrt ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) ≤ H * Real.sqrt H / 8 := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (H * Real.sqrt H / 8) ^ 2 = H ^ 3 / 64 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hH0.le]; ring
        rw [this]; exact hXX
      have hs2 : Real.sqrt H ≤ Real.sqrt (2000 * H) :=
        Real.sqrt_le_sqrt (by linarith)
      have : ε * Real.sqrt ((2 : ℝ) ^ i * Real.sqrt (2 ^ i)) ≤ 1 * (H * Real.sqrt H / 8) :=
        mul_le_mul (by linarith) hs1 (Real.sqrt_nonneg _) (by norm_num)
      have : H * Real.sqrt H / 8 ≤ H * Real.sqrt (2000 * H) :=
        by nlinarith [Real.sqrt_nonneg H]
      linarith
    have hK : Bq H ε i < 2 ^ (Jmax H + 1) := by
      have hc0 : ⌈H⌉₊ ≠ 0 := by have := Nat.le_ceil H; positivity
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌈H⌉₊
      have h1 : (⌈H⌉₊ : ℝ) < 2 ^ (Nat.log 2 ⌈H⌉₊ + 1) := by exact_mod_cast this
      have h2 : (2 : ℝ) ^ (Nat.log 2 ⌈H⌉₊ + 1) ≤ 2 ^ (Jmax H + 1) :=
        pow_le_pow_right₀ (by norm_num) (by simp only [Jmax]; omega)
      linarith [Nat.le_ceil H]
    have hcnt := DyadicCount.count hA2 hB0 hK
    have hJeq : (J H ε i : ℝ) = (((Finset.range (Jmax H + 1)).filter fun j : ℕ =>
        Aq H ε i ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ Bq H ε i).card : ℝ) := by
      congr 1
      simp only [J]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨-, hj⟩, hg⟩
        exact ⟨by omega, (good_iff hH0 hε0 hε1 hi h4).mp hg⟩
      · rintro ⟨hj, hAB⟩
        have hg := (good_iff hH0 hε0 hε1 hi h4).mpr hAB
        exact ⟨⟨hg.hj, by omega⟩, hg⟩
    rw [hJeq]
    rw [logb_A hH0 hε0, logb_B hH0 hε0] at hcnt
    -- `log₂ B - log₂ A = g - err`
    set δ := max (2 + e) (3 + i - h) - max 0 (i - h)
    have hδ1 : 2 ≤ δ := by
      simp only [δ]
      rcases le_total 0 ((i : ℝ) - h) with h0 | h0
      · rw [max_eq_right h0]; linarith [le_max_right (2 + e) (3 + i - h)]
      · rw [max_eq_left h0]; linarith [le_max_left (2 + e) (3 + i - h)]
    have hδ2 : δ ≤ 3 + e := by
      simp only [δ]
      have : max (2 + e) (3 + i - h) ≤ max 0 (i - h) + 3 + e := max_le
        (by linarith [le_max_left 0 ((i : ℝ) - h)]) (by linarith [le_max_right 0 ((i : ℝ) - h)])
      linarith
    have hba : -e + 3 * i / 4 - c / 2 - h / 2 - max (2 + e) (3 + i - h) =
        MainIntegral.g h i - (e + c / 2 + δ) := by rw [hg]; simp only [δ]; ring
    rw [hba] at hcnt
    obtain ⟨hl, hu⟩ := hcnt
    set m := MainIntegral.g h i
    have hmx : max 0 (m - (e + c / 2 + δ)) ≤ max 0 m :=
      max_le_max le_rfl (by linarith)
    have hmx2 : max 0 m - (e + c / 2 + δ) ≤ max 0 (m - (e + c / 2 + δ)) := by
      rcases le_total 0 m with h0 | h0
      · rw [max_eq_right h0]; exact le_max_right _ _
      · rw [max_eq_left h0]; linarith [le_max_left 0 (m - (e + c / 2 + δ))]
    rw [abs_le]
    have hJ0 : (0 : ℝ) ≤ (((Finset.range (Jmax H + 1)).filter fun j : ℕ =>
        Aq H ε i ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ Bq H ε i).card : ℝ) := Nat.cast_nonneg _
    simp only [D]
    constructor
    · -- lower
      rcases le_total 0 m with h0 | h0
      · rw [max_eq_right h0]; linarith
      · rw [max_eq_left h0]; linarith
    · linarith
  · -- no good pieces
    have hJ0 : J H ε i = 0 := by
      simp only [J]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hg
      exact absurd hg.g4 (not_le.mpr h4)
    rw [hJ0, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (le_max_left _ _)]
    have hgi : MainIntegral.g h i ≤ h / 2 - i / 4 := min_le_right _ _
    have hih : 2 * h - 4 < i := by
      have := (logb_lt_logb_iff (b := 2) (by norm_num) (by positivity) (by positivity)).mpr h4
      rw [logb_pow, logb_mul (by norm_num) (by positivity), logb_two_pow,
        show (16 : ℝ) = 2 ^ 4 by norm_num, logb_two_pow] at this
      push_cast at this; linarith
    simp only [D]
    apply max_le
    · positivity
    · linarith


theorem logb_H_ge {H : ℝ} (hH : 3 ≤ H) : 1 ≤ logb 2 H := by
  rw [show (1 : ℝ) = logb 2 2 by rw [logb_self_eq_one (by norm_num)]]
  exact (logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr (by linarith)

theorem J_zero {H ε : ℝ} {i : ℕ} (h4 : H ^ 2 < 16 * (2 : ℝ) ^ i) : J H ε i = 0 := by
  simp only [J]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hg
  exact absurd hg.g4 (not_le.mpr h4)

/-- **The sum of the scales of good pieces**: `Σ_{good} i = (11/54) h³ + O(D h²)`. -/
theorem sum_scales {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    |∑ p ∈ G H ε, (p.1 : ℝ) - 11 / 54 * logb 2 H ^ 3| ≤
      D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2 := by
  have hH0 : 0 < H := by linarith
  set h := logb 2 H
  have hh := logb_H_ge hH
  set N := ⌈2 * h⌉₊
  have hN1 : 2 * h ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 2 * h + 2 := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * h)]
  set R := max (Imax H) N
  -- `Imax ≤ 2h + 1`
  have hNmax : (Nmax H : ℝ) ≤ 2 * H ^ 2 := Cubic.BoxAsymptotic.Bands.Nmax_le hH
  have hNm1 : 1 ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
  have hImax : (Imax H : ℝ) ≤ 2 * h + 1 := by
    have hp := Nat.pow_log_le_self 2 (show Nmax H ≠ 0 by omega)
    have : (2 : ℝ) ^ Imax H ≤ 2 * H ^ 2 := by
      have h' : ((2 ^ Imax H : ℕ) : ℝ) ≤ Nmax H := by exact_mod_cast hp
      push_cast at h'; exact h'.trans hNmax
    have := (logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr this
    rw [logb_two_pow, logb_mul (by norm_num) (by positivity), logb_pow,
      logb_self_eq_one (by norm_num)] at this
    push_cast at this; linarith
  have hR : (R : ℝ) ≤ 2 * h + 2 := by
    rcases le_total (Imax H) N with hl | hl
    · rw [show R = N from max_eq_right hl]; exact hN2
    · rw [show R = Imax H from max_eq_left hl]; linarith
  -- extend both sums to `[1, R]`
  have hsum1 : ∑ p ∈ G H ε, (p.1 : ℝ) = ∑ i ∈ Finset.Icc 1 R, (i : ℝ) * J H ε i := by
    rw [sum_G_fst]
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (le_max_left _ _)) fun i hi hni => ?_
    have hi' : Imax H < i := by
      simp only [Finset.mem_Icc] at hi hni; omega
    have : H ^ 2 < 16 * (2 : ℝ) ^ i := by
      have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nmax H)
      have h2 : (Nmax H : ℝ) < 2 ^ i := by
        have : Nmax H < 2 ^ i := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hi')
        exact_mod_cast this
      have h3 : H ^ 2 + 3 * H - 1 < (Nmax H : ℝ) := by
        have := Nat.lt_floor_add_one (H ^ 2 + 3 * H)
        simp only [Cubic.BoxAsymptotic.Admissible.Nmax]; linarith
      nlinarith
    rw [J_zero this]; simp
  have hsum2 : ∑ i ∈ Finset.Icc 1 N, MainIntegral.F h i =
      ∑ i ∈ Finset.Icc 1 R, (i : ℝ) * max 0 (MainIntegral.g h i) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (le_max_right _ _)) (fun i hi hni => ?_)
      |>.trans (Finset.sum_congr rfl fun i _ => rfl)
    have : 2 * h ≤ (i : ℝ) := by
      simp only [Finset.mem_Icc] at hi hni
      have : N < i := by omega
      have : (N : ℝ) < i := by exact_mod_cast this
      linarith
    exact MainIntegral.F_zero this
  have hriem := MainIntegral.riemann hh hN1 hN2
  rw [hsum2] at hriem
  rw [hsum1]
  have hdiff : |∑ i ∈ Finset.Icc 1 R, (i : ℝ) * J H ε i -
      ∑ i ∈ Finset.Icc 1 R, (i : ℝ) * max 0 (MainIntegral.g h i)| ≤ D ε * (2 * h + 2) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Icc 1 R, |(i : ℝ) * J H ε i - i * max 0 (MainIntegral.g h i)| ≤
        (2 * h + 2) * D ε := by
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hiR : (i : ℝ) ≤ 2 * h + 2 :=
        (by exact_mod_cast (Finset.mem_Icc.mp hi).2 : (i : ℝ) ≤ R).trans hR
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul hiR (J_bound hH hε0 hε1 hi1) (abs_nonneg _) (by linarith)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : ((R + 1 - 1 : ℕ) : ℝ) ≤ 2 * h + 2 := by simp only [Nat.add_sub_cancel]; exact hR
    have hD0 : 0 ≤ D ε := by
      have := e_nonneg hε0 hε1
      have : 0 ≤ logb 2 2000 := logb_nonneg (by norm_num) (by norm_num)
      simp only [D]; positivity
    calc ((R + 1 - 1 : ℕ) : ℝ) * ((2 * h + 2) * D ε) ≤ (2 * h + 2) * ((2 * h + 2) * D ε) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = D ε * (2 * h + 2) ^ 2 := by ring
  calc |∑ i ∈ Finset.Icc 1 R, (i : ℝ) * J H ε i - 11 / 54 * h ^ 3|
      ≤ |∑ i ∈ Finset.Icc 1 R, (i : ℝ) * J H ε i -
          ∑ i ∈ Finset.Icc 1 R, (i : ℝ) * max 0 (MainIntegral.g h i)| +
        |∑ i ∈ Finset.Icc 1 R, (i : ℝ) * max 0 (MainIntegral.g h i) - 11 / 54 * h ^ 3| :=
        abs_sub_le _ _ _
    _ ≤ D ε * (2 * h + 2) ^ 2 + 16 * h ^ 2 := add_le_add hdiff hriem

end Cubic.BoxAsymptotic.GoodCount
