import Cubic.Analysis.PerronKernel
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Truncated Perron formula

For `a : ℕ → ℂ` with `∑ |a n| n^{-c} < ∞`, `0 < c ≤ 2`, `T ≥ 1` and `X > 0` not an integer,
`|∑_{1 ≤ n ≤ X} a n - (1 / 2πi) ∫_{c - iT}^{c + iT} (∑ a n n^{-s}) X^s / s ds|`
is at most `∑_n |a n| (X/n)^c min(4, 1 / (π T |log (X/n)|))`.

The Dirichlet series is integrated termwise (dominated convergence, since
`|a n n^{-s} X^s / s| ≤ |a n| n^{-c} X^c / c` on the segment), which writes the integral as
`∑ a n I(X/n, c, T)`; the two kernel bounds of `Cubic.Analysis.PerronKernel` finish the proof.
-/

noncomputable section

namespace Cubic.Analysis.Perron

open Complex Set Filter Topology MeasureTheory intervalIntegral LSeries

/-- The truncated Perron integral
`(1 / 2πi) ∫_{c - iT}^{c + iT} (∑ a n n^{-s}) X^s / s ds`,
written as a real integral over `s = c + it` with `ds = i dt`. -/
def perronIntegral (a : ℕ → ℂ) (c T X : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∫ t in (-T)..T,
    LSeries a ((c : ℂ) + t * I) * (X : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I

/-- `a n n^{-s} X^s = a n (X / n)^s` for `n ≥ 1` and `X > 0`. -/
lemma term_mul_cpow (a : ℕ → ℂ) {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term a s n * (X : ℂ) ^ s = a n * ((X / n : ℝ) : ℂ) ^ s := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have harg : (n : ℂ).arg ≠ Real.pi := by rw [natCast_arg]; exact Real.pi_ne_zero.symm
  have hns : (n : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hn))
  rw [term_of_ne_zero hn, div_eq_mul_inv X, Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg hX.le (inv_nonneg.2 hn'.le), Complex.ofReal_inv,
    Complex.ofReal_natCast, inv_cpow _ _ harg]
  field_simp

/-- Termwise integration: the Perron integral equals `∑_{n ≥ 1} a n I(X/n, c, T)`. -/
lemma hasSum_perronIntegral {a : ℕ → ℂ} {c T X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (ha : LSeriesSummable a c) :
    HasSum (fun n => if n = 0 then 0 else a n * kernel (X / n) c T)
      (perronIntegral a c T X) := by
  set s : ℝ → ℂ := fun t => (c : ℂ) + t * I with hs_def
  have hs_cont : Continuous s := by fun_prop
  have hs0 : ∀ t, s t ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp [s] at this
    linarith
  have hsre : ∀ t, (s t).re = c := fun t => by simp [s]
  have hsn : ∀ t, c ≤ ‖s t‖ := fun t => by
    simpa [hsre t, abs_of_pos hc] using Complex.abs_re_le_norm (s t)
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  set F : ℕ → ℝ → ℂ := fun n t => term a (s t) n * ((X : ℂ) ^ (s t) / s t * I) with hF_def
  have hterm : ∀ n, Continuous fun t => term a (s t) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero]
      exact continuous_const
    · simp only [term_of_ne_zero hn]
      refine continuous_const.div
        ((continuous_id.const_cpow (Or.inl (by exact_mod_cast hn))).comp hs_cont) fun t => ?_
      exact cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hn))
  have hFc : ∀ n, Continuous (F n) := fun n =>
    (hterm n).mul ((((continuous_id.const_cpow (Or.inl hX')).comp hs_cont).div hs_cont
      hs0).mul continuous_const)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -T) (b := T) (F := F)
    (f := fun t => LSeries a (s t) * ((X : ℂ) ^ (s t) / s t * I))
    (fun n _ => ‖term a c n‖ * (X ^ c / c))
    (fun n => (hFc n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t _ => by
      simp only [F, norm_mul, norm_div, norm_I, mul_one, norm_cpow_eq_rpow_re_of_pos hX,
        hsre t]
      have hnt : ‖term a (s t) n‖ = ‖term a c n‖ := by
        rw [norm_term_eq, norm_term_eq, hsre t, Complex.ofReal_re]
      rw [hnt]
      gcongr
      exact hsn t)
    (Eventually.of_forall fun t _ =>
      (summable_norm_iff.2 ha).mul_right _)
    _root_.intervalIntegrable_const
    (Eventually.of_forall fun t _ =>
      ((ha.of_re_le_re (by rw [hsre t, Complex.ofReal_re])).LSeriesHasSum).mul_right _)
  have hInt : ∀ n, (2 * Real.pi * I)⁻¹ * ∫ t in (-T)..T, F n t =
      if n = 0 then 0 else a n * kernel (X / n) c T := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · rw [if_neg hn, kernel]
      have : ∀ t, F n t = a n * (((X / n : ℝ) : ℂ) ^ (s t) / s t * I) := fun t => by
        simp only [F]
        rw [show term a (s t) n * ((X : ℂ) ^ (s t) / s t * I) =
          (term a (s t) n * (X : ℂ) ^ (s t)) / s t * I by ring, term_mul_cpow a hX hn]
        ring
      simp only [this, intervalIntegral.integral_const_mul, s]
      ring
  have hmain := hsum.mul_left (2 * Real.pi * I)⁻¹
  simp only [hInt] at hmain
  convert hmain using 2
  rw [perronIntegral]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [s]
  ring

/-- **Truncated Perron formula.** Let `a : ℕ → ℂ` with `∑ |a n| n^{-c} < ∞`, where
`0 < c ≤ 2`; let `T ≥ 1` and let `X > 0` be different from every integer. Then
`|∑_{1 ≤ n ≤ X} a n - (1 / 2πi) ∫_{c - iT}^{c + iT} (∑ a n n^{-s}) X^s / s ds|`
is at most `∑_n |a n| (X/n)^c min(4, 1 / (π T |log (X/n)|))`.
The `n = 0` term of the bound vanishes since `(X / 0)^c = 0^c = 0`. -/
theorem norm_sum_sub_perronIntegral_le (a : ℕ → ℂ) {c T X : ℝ} (hc : 0 < c) (hc2 : c ≤ 2)
    (hT : 1 ≤ T) (hX : 0 < X) (hXn : ∀ n : ℕ, (n : ℝ) ≠ X) (ha : LSeriesSummable a c) :
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, a n - perronIntegral a c T X‖ ≤
      ∑' n : ℕ, ‖a n‖ * (X / n) ^ c * min 4 (1 / (Real.pi * T * |Real.log (X / n)|)) := by
  have hT0 : 0 < T := by linarith
  set E : ℕ → ℝ := fun n =>
    ‖a n‖ * (X / n) ^ c * min 4 (1 / (Real.pi * T * |Real.log (X / n)|)) with hE_def
  have hmin0 : ∀ n : ℕ, 0 ≤ min 4 (1 / (Real.pi * T * |Real.log (X / n)|)) := fun n =>
    le_min (by norm_num) (by positivity)
  have hE0 : E 0 = 0 := by simp [E, Real.zero_rpow hc.ne']
  have hQ : HasSum (fun n => if n ∈ Finset.Icc 1 ⌊X⌋₊ then a n else 0)
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, a n) := by
    have h0 := hasSum_sum_of_ne_finset_zero (s := Finset.Icc 1 ⌊X⌋₊)
      (f := fun n => if n ∈ Finset.Icc 1 ⌊X⌋₊ then a n else 0)
      (L := SummationFilter.unconditional ℕ) (fun n hn => if_neg hn)
    rwa [Finset.sum_congr rfl fun n hn => if_pos hn] at h0
  have hD := hQ.sub (hasSum_perronIntegral (T := T) hc hX ha)
  have hEsum : Summable E := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg hX.le (Nat.cast_nonneg n)) _)) (hmin0 n)) (fun n => ?_)
      ((summable_norm_iff.2 ha).mul_left (4 * X ^ c))
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [norm_term_eq, if_neg hn, Complex.ofReal_re]
      simp only [E]
      rw [Real.div_rpow hX.le hn'.le]
      have h4 := min_le_left 4 (1 / (Real.pi * T * |Real.log (X / n)|))
      have hXc := Real.rpow_pos_of_pos hX c
      have hnc := Real.rpow_pos_of_pos hn' c
      calc ‖a n‖ * (X ^ c / n ^ c) * min 4 (1 / (Real.pi * T * |Real.log (X / n)|))
          ≤ ‖a n‖ * (X ^ c / n ^ c) * 4 := by gcongr
        _ = 4 * X ^ c * (‖a n‖ / n ^ c) := by ring
  refine hD.norm_le_of_bounded hEsum.hasSum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hE0]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hy : 0 < X / n := div_pos hX hn'
    have hy1 : X / n ≠ 1 := fun h => hXn n ((div_eq_one_iff_eq hn'.ne').1 h).symm
    have hmem : n ∈ Finset.Icc 1 ⌊X⌋₊ ↔ 1 < X / n := by
      rw [Finset.mem_Icc, one_lt_div hn', Nat.le_floor_iff hX.le]
      exact ⟨fun h => lt_of_le_of_ne h.2 (hXn n), fun h => ⟨Nat.one_le_iff_ne_zero.2 hn, h.le⟩⟩
    have heq : (if n ∈ Finset.Icc 1 ⌊X⌋₊ then a n else 0) -
        (if n = 0 then 0 else a n * kernel (X / n) c T) =
        -(a n * (kernel (X / n) c T - (if 1 < X / n then 1 else 0))) := by
      rw [if_neg hn]
      by_cases h : 1 < X / n
      · rw [if_pos (hmem.2 h), if_pos h]; ring
      · rw [if_neg (fun h' => h (hmem.1 h')), if_neg h]; ring
    rw [heq, norm_neg, norm_mul]
    have hk := le_min (norm_kernel_sub_indicator_le_four hy hc hc2 hT)
      (norm_kernel_sub_indicator_le hy hy1 hc hT0)
    rw [div_eq_mul_one_div ((X / n) ^ c), mul_comm 4 ((X / n) ^ c),
      ← mul_min_of_nonneg _ _ (Real.rpow_nonneg hy.le c)] at hk
    simp only [E]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)

end Cubic.Analysis.Perron
