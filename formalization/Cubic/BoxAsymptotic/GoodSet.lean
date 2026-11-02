import Cubic.BoxAsymptotic.BulkW

/-!
# The set of good pieces

All good `(i, j)` have `1 ≤ i ≤ log₂ N(H)` (since `2^i ≤ H²/16`) and `2 ≤ j ≤ log₂ ⌈H⌉ + 2`
(since `2000 H ≤ ε² Θ² X √X` forces `Θ ≥ 1/H`). There are `O(log² H)` of them.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.GoodSet

open Cubic.BoxAsymptotic.Admissible (Nmax)
open Cubic.BoxAsymptotic.Bands (card_bands Nmax_le)
open Cubic.BoxAsymptotic.BulkW (Good)
open scoped Classical

def Imax (H : ℝ) : ℕ := Nat.log 2 (Nmax H)

def Jmax (H : ℝ) : ℕ := Nat.log 2 ⌈H⌉₊ + 2

/-- The good pieces. -/
def G (H ε : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (Imax H)) ×ˢ (Finset.Icc 2 (Jmax H))).filter fun p => Good H ε p.1 p.2

theorem mem_G {H ε : ℝ} {p : ℕ × ℕ} : p ∈ G H ε → Good H ε p.1 p.2 := fun h =>
  (Finset.mem_filter.mp h).2

/-- A good piece has `2^j ≤ H` (so `Θ ≥ 1/H`). -/
theorem two_pow_le {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) {i j : ℕ}
    (hg : Good H ε i j) : (2 : ℝ) ^ j ≤ H := by
  set X : ℝ := 2 ^ i
  set Θ : ℝ := (1 / 2) ^ j
  have hX : 0 < X := by positivity
  have hΘ : 0 < Θ := by positivity
  have h2 : 2000 * H ≤ ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X) := hg.g2
  have h4 : 16 * X ≤ H ^ 2 := hg.g4
  have hsX : Real.sqrt X ≤ H / 4 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hXX : X * Real.sqrt X ≤ H ^ 3 / 64 := by
    have := mul_le_mul (by linarith : X ≤ H ^ 2 / 16) hsX (Real.sqrt_nonneg _) (by positivity)
    have e : H ^ 2 / 16 * (H / 4) = H ^ 3 / 64 := by ring
    linarith
  have hε2 : ε ^ 2 ≤ 1 / 100 := by nlinarith
  have hH0 : 0 < H := by linarith
  have hΘH : 1 ≤ Θ * H := by
    have : 2000 * H ≤ 1 / 100 * Θ ^ 2 * (H ^ 3 / 64) := by
      calc 2000 * H ≤ ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X) := h2
        _ ≤ 1 / 100 * Θ ^ 2 * (H ^ 3 / 64) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hε2 (by positivity)) hXX (by positivity)
            (by positivity)
    have : 1 ≤ (Θ * H) ^ 2 := by nlinarith
    nlinarith [mul_pos hΘ hH0]
  have e : (2 : ℝ) ^ j * Θ = 1 := by simp only [Θ]; rw [← mul_pow]; norm_num
  nlinarith

theorem mem_G_of_good {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) {i j : ℕ}
    (hg : Good H ε i j) : (i, j) ∈ G H ε := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hg.hi, ?_⟩,
    Finset.mem_Icc.mpr ⟨hg.hj, ?_⟩⟩, hg⟩
  · -- `2^i ≤ N(H)`
    have h4 := hg.g4
    have : 2 ^ i ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
    have := Nat.log_mono_right (b := 2) this
    rwa [Nat.log_pow (by norm_num)] at this
  · -- `2^j ≤ H`
    set X : ℝ := 2 ^ i
    set Θ : ℝ := (1 / 2) ^ j
    have hX : 0 < X := by positivity
    have hΘ : 0 < Θ := by positivity
    have h2 : 2000 * H ≤ ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X) := hg.g2
    have h4 : 16 * X ≤ H ^ 2 := hg.g4
    have hsX : Real.sqrt X ≤ H / 4 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hXX : X * Real.sqrt X ≤ H ^ 3 / 64 := by
      have := mul_le_mul (by linarith : X ≤ H ^ 2 / 16) hsX (Real.sqrt_nonneg _) (by positivity)
      have e : H ^ 2 / 16 * (H / 4) = H ^ 3 / 64 := by ring
      linarith
    have hε2 : ε ^ 2 ≤ 1 / 100 := by nlinarith
    have hH0 : 0 < H := by linarith
    have hΘH : 1 ≤ Θ * H := by
      have : 2000 * H ≤ 1 / 100 * Θ ^ 2 * (H ^ 3 / 64) := by
        calc 2000 * H ≤ ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X) := h2
          _ ≤ 1 / 100 * Θ ^ 2 * (H ^ 3 / 64) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hε2 (by positivity)) hXX (by positivity)
              (by positivity)
      have : 1 ≤ (Θ * H) ^ 2 := by nlinarith
      nlinarith [mul_pos hΘ hH0]
    have hj : (2 : ℝ) ^ j ≤ H := by
      have e : (2 : ℝ) ^ j * Θ = 1 := by simp only [Θ]; rw [← mul_pow]; norm_num
      nlinarith
    have : 2 ^ j ≤ ⌈H⌉₊ := by
      have : ((2 ^ j : ℕ) : ℝ) ≤ ⌈H⌉₊ := by push_cast; exact hj.trans (Nat.le_ceil H)
      exact_mod_cast this
    have := Nat.log_mono_right (b := 2) this
    rw [Nat.log_pow (by norm_num)] at this
    simp only [Jmax]; omega

theorem card_G {H ε : ℝ} (hH : 3 ≤ H) : ((G H ε).card : ℝ) ≤ 30 * Real.log H ^ 2 := by
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have h1 : (G H ε).card ≤ (Imax H) * (Jmax H) := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hI : (Imax H : ℝ) ≤ 6 * Real.log H := by
    have := card_bands hH; push_cast at this; simp only [Imax]; linarith
  have hJ : (Jmax H : ℝ) ≤ 5 * Real.log H := by
    have hc : ⌈H⌉₊ ≠ 0 := by have := Nat.le_ceil H; positivity
    have hp := Nat.pow_log_le_self 2 hc
    have hl : ((Nat.log 2 ⌈H⌉₊ : ℕ) : ℝ) * Real.log 2 ≤ Real.log (H + 1) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity)
        ((by exact_mod_cast hp : ((2 ^ Nat.log 2 ⌈H⌉₊ : ℕ) : ℝ) ≤ ⌈H⌉₊).trans
          (Nat.ceil_lt_add_one (by linarith)).le |>.trans_eq' (by push_cast; rfl))
    have hlH1 : Real.log (H + 1) ≤ Real.log H + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    simp only [Jmax]; push_cast
    have : ((Nat.log 2 ⌈H⌉₊ : ℕ) : ℝ) ≤ 2 * Real.log H + 1 := by
      have : ((Nat.log 2 ⌈H⌉₊ : ℕ) : ℝ) * Real.log 2 ≤ Real.log H + 1 := by linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌈H⌉₊)]
    linarith
  calc ((G H ε).card : ℝ) ≤ (Imax H : ℝ) * Jmax H := by exact_mod_cast h1
    _ ≤ (6 * Real.log H) * (5 * Real.log H) :=
        mul_le_mul hI hJ (Nat.cast_nonneg _) (by linarith)
    _ = 30 * Real.log H ^ 2 := by ring

end Cubic.BoxAsymptotic.GoodSet
