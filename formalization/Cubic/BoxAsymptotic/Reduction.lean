import Cubic.BoxAsymptotic.Bands

/-!
# `eq:continuous`: `N_□(H) = Σ_n ∫ W_H dμ_n + O(H log² H)`

`2 (N_□(H) + #split) = #pairs = Σ_{β, B ≠ 0} #{s ≡ s₀(β) : s ∈ E}` (`SquareDiscriminant`,
`Admissible`). Each term is `W/3` up to `12` (`LatticeCount.trace_count`), and only the `β`
with `E ≠ ∅` contribute an error, `O(H log² H)` of them (`Bands.card_nonempty`). The real
`β` (`B = 0`) contribute `O(H log H)` to `Σ W` (`Bands.sum_real`), and the split
polynomials `O(H log² H)` (`SplitCount.split_count`). With `μ_n` of mass `1/6` per
admissible `β`, `Σ_n ∫ W dμ_n = (1/6) Σ_β W`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Reduction

open Cubic.BoxAsymptotic.Admissible Cubic.BoxAsymptotic.Bands
open Cubic.BoxAsymptotic.TraceWidth (E W W_nonneg)
open Cubic.BoxAsymptotic.LatticeCount (traceSet trace_count)
open scoped Classical

theorem trace_err {H : ℝ} (x : ℕ × (ℤ × ℤ)) :
    |((traceSet H x.1 (θ x.2) (s₀ x.1 x.2)).card : ℝ) - W H x.1 (θ x.2) / 3| ≤
      if (E H x.1 (θ x.2)).Nonempty then 12 else 0 := by
  split_ifs with h
  · exact trace_count _ _ _ _
  · have he : E H x.1 (θ x.2) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have ht : traceSet H x.1 (θ x.2) (s₀ x.1 x.2) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun s _ hs => by rw [he] at hs; exact hs.2
    rw [ht, W, he]; simp

/-- **`eq:continuous`**. -/
theorem reduction : ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 3 ≤ H →
    |(CubicTargets.BoxHeight.boxCount H : ℝ) - (1 / 6) * ∑ x ∈ Bset H, W H x.1 (θ x.2)| ≤
      K * H * Real.log H ^ 2 := by
  obtain ⟨K₁, hK₁, h1⟩ := card_nonempty
  obtain ⟨K₂, hK₂, h2⟩ := sum_real
  refine ⟨6 * K₁ + K₂ + 216, by positivity, fun H hH => ?_⟩
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  set B := Bset H
  set F := B.filter fun x : ℕ × (ℤ × ℤ) => x.2.2 ≠ 0
  set G := B.filter fun x : ℕ × (ℤ × ℤ) => x.2.2 = 0
  have hpairs := card_pairs_sum H
  have heq := Cubic.BoxAsymptotic.SquareDiscriminant.card_pairs_eq H
  have hsplit := Cubic.BoxAsymptotic.SplitCount.split_count (H := H) (by linarith)
  -- the lattice errors
  have herr : |(∑ x ∈ F, ((traceSet H x.1 (θ x.2) (s₀ x.1 x.2)).card : ℝ)) -
      ∑ x ∈ F, W H x.1 (θ x.2) / 3| ≤ 12 * (K₁ * H * Real.log H ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => trace_err (H := H) x).trans ?_
    calc ∑ x ∈ F, (if (E H x.1 (θ x.2)).Nonempty then (12 : ℝ) else 0)
        ≤ ∑ x ∈ B, (if (E H x.1 (θ x.2)).Nonempty then (12 : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by split_ifs <;> norm_num
      _ = 12 * ((B.filter fun x : ℕ × (ℤ × ℤ) => (E H x.1 (θ x.2)).Nonempty).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 12 * (K₁ * H * Real.log H ^ 2) := by linarith [h1 H hH]
  -- the real `β`
  have hsplitW : ∑ x ∈ B, W H x.1 (θ x.2) = ∑ x ∈ F, W H x.1 (θ x.2) +
      ∑ x ∈ G, W H x.1 (θ x.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun x : ℕ × (ℤ × ℤ) => x.2.2 ≠ 0)]
    congr 1
    refine Finset.sum_congr (by ext x; simp [G]) fun _ _ => rfl
  have hG := h2 H hH
  have hG0 : 0 ≤ ∑ x ∈ G, W H x.1 (θ x.2) := Finset.sum_nonneg fun x _ => W_nonneg _ _ _
  have hS0 : (0 : ℝ) ≤ Nat.card (SquareDiscriminant.splitSet H) := Nat.cast_nonneg _
  have hcast : (∑ x ∈ F, ((traceSet H x.1 (θ x.2) (s₀ x.1 x.2)).card : ℝ)) =
      2 * ((CubicTargets.BoxHeight.boxCount H : ℝ) +
        Nat.card (SquareDiscriminant.splitSet H)) := by
    rw [← Nat.cast_sum, ← hpairs, heq]; push_cast; ring
  rw [hsplitW]
  rw [hcast, ← Finset.sum_div] at herr
  rw [abs_le] at herr ⊢
  have hL2 : H * Real.log H ≤ H * Real.log H ^ 2 := by
    have : Real.log H ≤ Real.log H ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  constructor <;> nlinarith

end Cubic.BoxAsymptotic.Reduction
