import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting dyadic scales in an interval

`#{j : A ≤ 2^j ≤ B}` differs from `max(0, log₂ B - log₂ A)` by at most `1`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.DyadicCount

open Real

theorem two_pow_le_iff {x : ℝ} (hx : 0 < x) (j : ℕ) : (2 : ℝ) ^ j ≤ x ↔ (j : ℝ) ≤ logb 2 x := by
  rw [le_logb_iff_rpow_le (by norm_num) hx, rpow_natCast]

theorem le_two_pow_iff {x : ℝ} (hx : 0 < x) (j : ℕ) : x ≤ (2 : ℝ) ^ j ↔ logb 2 x ≤ j := by
  rw [logb_le_iff_le_rpow (by norm_num) hx, rpow_natCast]

open scoped Classical in
/-- `log₂(B/A) - 1 ≤ #{j < K : A ≤ 2^j ≤ B} ≤ max(0, log₂(B/A)) + 1` for `2 ≤ A`, `0 < B < 2^K`. -/
theorem count {A B : ℝ} (hA : 2 ≤ A) (hB : 0 < B) {K : ℕ} (hK : B < 2 ^ K) :
    logb 2 B - logb 2 A - 1 ≤
        (((Finset.range K).filter fun j : ℕ => A ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ B).card : ℝ) ∧
      (((Finset.range K).filter fun j : ℕ => A ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ B).card : ℝ) ≤
        max 0 (logb 2 B - logb 2 A) + 1 := by
  set a := logb 2 A
  set b := logb 2 B
  have ha1 : 1 ≤ a := by
    rw [show (1 : ℝ) = logb 2 2 by rw [logb_self_eq_one (by norm_num)]]
    exact (logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr hA
  have ha : 0 ≤ a := by linarith
  have hbK : b < K := by
    rw [← rpow_natCast] at hK
    exact (logb_lt_iff_lt_rpow (by norm_num) hB).mpr hK
  have hS : ((Finset.range K).filter fun j : ℕ => A ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ B) =
      Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    rw [le_two_pow_iff (by linarith) j, two_pow_le_iff hB j, Nat.ceil_le]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      have hj1 : 1 ≤ j := by
        have : (1 : ℝ) ≤ j := by linarith
        exact_mod_cast this
      have hb0 : 0 ≤ b := by
        by_contra hneg; push_neg at hneg
        have : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      have hjb : (j : ℝ) ≤ b := (Nat.cast_le.mpr h2).trans (Nat.floor_le hb0)
      refine ⟨?_, h1, hjb⟩
      exact_mod_cast (show (j : ℝ) < K by linarith)
  rw [hS, Nat.card_Icc]
  constructor
  · -- lower bound
    have h1 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
    rcases le_or_gt 0 b with hb | hb
    · have h2 : b - 1 < (⌊b⌋₊ : ℝ) := Nat.sub_one_lt_floor b
      have : ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) ≥ (⌊b⌋₊ : ℝ) + 1 - ⌈a⌉₊ := by
        rcases le_or_gt ⌈a⌉₊ (⌊b⌋₊ + 1) with h | h
        · rw [Nat.cast_sub h]; push_cast; linarith
        · rw [Nat.sub_eq_zero_of_le h.le]; push_cast
          have : ((⌊b⌋₊ + 1 : ℕ) : ℝ) < ⌈a⌉₊ := by exact_mod_cast h
          push_cast at this; linarith
      linarith
    · have : (0 : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · -- upper bound
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    rcases le_or_gt ⌈a⌉₊ (⌊b⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast
      rcases le_or_gt 0 b with hb | hb
      · have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
        linarith [le_max_right 0 (b - a)]
      · have : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [this]; push_cast
        linarith [le_max_left 0 (b - a)]
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast
      linarith [le_max_left 0 (b - a)]

end Cubic.BoxAsymptotic.DyadicCount
