import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Riemann sums over lattice points in `[-1, 1]`

Supporting estimate for `thm:generalMonicCount`. For `g` Lipschitz (constant `M`) and bounded
(by `B`) on `[-2, 2]`, and a step `0 < δ ≤ 1`, the sum of `δ g(kδ)` over `|k| ≤ ⌊1/δ⌋` differs
from `∫_{-1}^{1} g` by at most `(3M + 2B) δ`: each cell `[kδ, (k+1)δ]` contributes an error of
at most `Mδ²`, and the union of the cells differs from `[-1, 1]` by at most `δ` at each end.
-/

noncomputable section

namespace Cubic.Counting.RiemannSum

open MeasureTheory intervalIntegral

variable {g : ℝ → ℝ} {M B : ℝ}

theorem cell_bound (hg : Continuous g) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2, |g x - g y| ≤ M * |x - y|)
    {x δ : ℝ} (hδ : 0 ≤ δ) (hx : -2 ≤ x) (hxδ : x + δ ≤ 2) :
    |δ * g x - ∫ t in x..x + δ, g t| ≤ M * δ ^ 2 := by
  have hc : δ * g x = ∫ _ in x..x + δ, g x := by simp
  rw [hc, ← intervalIntegral.integral_sub intervalIntegrable_const
    (hg.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + δ)
    (C := M * δ) (f := fun t => g x - g t) (by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      have h1 := hM x ⟨hx, by linarith⟩ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [Real.norm_eq_abs]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hM0)
      rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
  rw [Real.norm_eq_abs, show x + δ - x = δ by ring, abs_of_nonneg hδ] at this
  linarith [show M * δ * δ = M * δ ^ 2 by ring]

theorem end_bound
    (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B) {a b : ℝ} (ha : -2 ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    |∫ t in a..b, g t| ≤ B * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := B)
    (f := g) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      exact hB t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [Real.norm_eq_abs, show |b - a| = b - a from abs_of_nonneg (by linarith)] at this
  linarith [show (b - a) * B = B * (b - a) by ring]

/-- The Riemann sum estimate. -/
theorem riemann (hg : Continuous g) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2, |g x - g y| ≤ M * |x - y|)
    (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN1 : N * δ ≤ 1) (hN2 : 1 < (N + 1) * δ) :
    |δ * ∑ k ∈ Finset.Icc (-(N : ℤ)) N, g (k * δ) - ∫ x in (-1 : ℝ)..1, g x| ≤
      (3 * M + 2 * B) * δ := by
  set a : ℕ → ℝ := fun j => ((j : ℝ) - N) * δ with ha
  have hreindex : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, g (k * δ) =
      ∑ j ∈ Finset.range (2 * N + 1), g (a j) := by
    refine Finset.sum_nbij' (fun k : ℤ => (k + N).toNat) (fun j : ℕ => (j : ℤ) - N) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      show ((k + N).toNat : ℤ) - N = k; omega
    · intro j _; simp
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [a]
      congr 1
      have : ((k + N).toNat : ℤ) = k + N := Int.toNat_of_nonneg (by omega)
      have h' : (((k + N).toNat : ℕ) : ℝ) = (k : ℝ) + N := by exact_mod_cast this
      rw [h']; ring
  have hadj : ∀ j, a (j + 1) = a j + δ := fun j => by simp only [a]; push_cast; ring
  have hsum : ∑ j ∈ Finset.range (2 * N + 1), ∫ t in a j..a (j + 1), g t =
      ∫ t in a 0..a (2 * N + 1), g t :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hg.intervalIntegrable _ _
  have hcells : |δ * ∑ j ∈ Finset.range (2 * N + 1), g (a j) - ∫ t in a 0..a (2 * N + 1), g t| ≤
      (2 * N + 1) * (M * δ ^ 2) := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j ∈ Finset.range (2 * N + 1), |δ * g (a j) - ∫ t in a j..a (j + 1), g t| ≤
        M * δ ^ 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : (j : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : j ≤ 2 * N)
      rw [hadj]
      refine cell_bound hg hM0 hM hδ0.le ?_ ?_
      · simp only [a]; nlinarith [Nat.cast_nonneg (α := ℝ) j]
      · simp only [a]; nlinarith
    refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
    simp
  -- the ends
  have ha0 : a 0 = -(N * δ) := by simp [a]
  have haN : a (2 * N + 1) = (N + 1) * δ := by simp only [a]; push_cast; ring
  have hsplit : ∫ t in a 0..a (2 * N + 1), g t =
      (∫ t in a 0..(-1), g t) + (∫ t in (-1 : ℝ)..1, g t) + ∫ t in (1 : ℝ)..a (2 * N + 1), g t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have he1 := end_bound hB (a := -1) (b := a 0) (by norm_num) (by rw [ha0]; nlinarith)
    (by rw [ha0]; linarith)
  rw [intervalIntegral.integral_symm, abs_neg] at he1
  have he2 := end_bound hB (a := 1) (b := a (2 * N + 1)) (by norm_num)
    (by rw [haN]; nlinarith) (by rw [haN]; linarith)
  rw [hreindex]
  have hNδ : (2 * N + 1) * (M * δ ^ 2) ≤ 3 * M * δ := by
    have : (2 * N + 1) * δ ≤ 3 := by nlinarith
    nlinarith [mul_nonneg hM0 hδ0.le]
  rw [hsplit] at hcells
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
  have e1 : B * (a 0 - -1) ≤ B * δ := mul_le_mul_of_nonneg_left (by rw [ha0]; nlinarith) hB0
  have e2 : B * (a (2 * N + 1) - 1) ≤ B * δ :=
    mul_le_mul_of_nonneg_left (by rw [haN]; nlinarith) hB0
  have hc2 := hcells.trans hNδ
  rw [abs_le] at hc2 he1 he2 ⊢
  constructor <;> linarith

end Cubic.Counting.RiemannSum
