import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The leading integral (`thm:main`, last display)

With `h = log₂ H` and `i = log₂ n`, the number of good angular pieces at scale `i` is
`g(i) + O(log(1/ε))` with `g(t) = min(3t/4 - h/2, h/2 - t/4)`: the logarithmic length
`log(min(1, H/n)/(H^{1/2} n^{-3/4}))` in base `2`. The draft's integral is

  `∫_0^{2h} t max(0, g(t)) dt = h³ (∫_{2/3}^1 v(3v/4 - 1/2) dv + ∫_1^2 v(1/2 - v/4) dv)`
  `= h³ (1/27 + 1/6) = (11/54) h³`,

and a Riemann sum over integers `t = i` differs from it by `O(h²)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.MainIntegral

/-- `g(t) = min(3t/4 - h/2, h/2 - t/4)`. -/
def g (h t : ℝ) : ℝ := min (3 * t / 4 - h / 2) (h / 2 - t / 4)

/-- `F(t) = t max(0, g(t))`. -/
def F (h t : ℝ) : ℝ := t * max 0 (g h t)

theorem g_cont (h : ℝ) : Continuous (g h) := by unfold g; fun_prop

theorem F_cont (h : ℝ) : Continuous (F h) := by
  unfold F
  exact continuous_id.mul (continuous_const.max (g_cont h))

theorem integral_F {h : ℝ} (hh : 0 < h) : ∫ t in (0 : ℝ)..2 * h, F h t = 11 / 54 * h ^ 3 := by
  have hc := F_cont h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (2 * h / 3))
      (hc.intervalIntegrable (2 * h / 3) (2 * h)),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (2 * h / 3) h)
      (hc.intervalIntegrable h (2 * h))]
  have h1 : ∫ t in (0 : ℝ)..(2 * h / 3), F h t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [F, g]
      rw [max_eq_left (min_le_of_left_le (by linarith [ht.2])), mul_zero]]
    simp
  have h2 : ∫ t in (2 * h / 3)..h, F h t = ∫ t in (2 * h / 3)..h, (3 / 4 * t ^ 2 - h / 2 * t) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [F, g]
      rw [min_eq_left (by linarith [ht.2]), max_eq_right (by linarith [ht.1])]; ring
  have h3 : ∫ t in h..(2 * h), F h t = ∫ t in h..(2 * h), (h / 2 * t - 1 / 4 * t ^ 2) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [F, g]
      rw [min_eq_right (by linarith [ht.1]), max_eq_right (by linarith [ht.2])]; ring
  rw [h1, h2, h3, zero_add]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => 3 / 4 * t ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => h / 2 * t).intervalIntegrable _ _),
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => h / 2 * t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => 1 / 4 * t ^ 2).intervalIntegrable _ _)]
  have e1 : ∀ a b : ℝ, ∫ t in a..b, h / 2 * t = h / 2 * ((b ^ 2 - a ^ 2) / 2) := fun a b => by
    rw [intervalIntegral.integral_const_mul, integral_id]
  have e2 : ∀ a b c : ℝ, ∫ t in a..b, c * t ^ 2 = c * ((b ^ 3 - a ^ 3) / 3) := fun a b c => by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  rw [e1, e1, e2, e2]
  ring


theorem mg_bounds (h t : ℝ) : 0 ≤ max 0 (g h t) ∧ max 0 (g h t) ≤ max 0 (h / 4) := by
  refine ⟨le_max_left _ _, max_le_max le_rfl ?_⟩
  simp only [g]
  rcases le_total t h with ht | ht
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

theorem mg_lip (h t s : ℝ) : |max 0 (g h t) - max 0 (g h s)| ≤ 3 / 4 * |t - s| := by
  refine (abs_max_sub_max_le_max 0 (g h t) 0 (g h s)).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  simp only [g]
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [show 3 * t / 4 - h / 2 - (3 * s / 4 - h / 2) = 3 / 4 * (t - s) by ring, abs_mul]
    norm_num
  · have : |h / 2 - t / 4 - (h / 2 - s / 4)| = 1 / 4 * |t - s| := by
      rw [show h / 2 - t / 4 - (h / 2 - s / 4) = (1 / 4) * (s - t) by ring, abs_mul,
        abs_sub_comm]
      norm_num
    rw [this]; linarith [abs_nonneg (t - s)]

theorem F_lip {h R t s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) (hsR : s ≤ R) :
    |F h t - F h s| ≤ (h / 4 + 3 / 4 * R) * |t - s| := by
  simp only [F]
  have ⟨m0, m1⟩ := mg_bounds h t
  rw [max_eq_right (by linarith : 0 ≤ h / 4)] at m1
  have hl := mg_lip h t s
  have e : t * max 0 (g h t) - s * max 0 (g h s) =
      (t - s) * max 0 (g h t) + s * (max 0 (g h t) - max 0 (g h s)) := by ring
  rw [e]
  calc |(t - s) * max 0 (g h t) + s * (max 0 (g h t) - max 0 (g h s))|
      ≤ |t - s| * max 0 (g h t) + s * |max 0 (g h t) - max 0 (g h s)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg m0, abs_of_nonneg hs]
    _ ≤ |t - s| * (h / 4) + R * (3 / 4 * |t - s|) :=
        add_le_add (mul_le_mul_of_nonneg_left m1 (abs_nonneg _))
          (mul_le_mul hsR hl (abs_nonneg _) (by linarith))
    _ = _ := by ring

theorem F_zero {h t : ℝ} (ht : 2 * h ≤ t) : F h t = 0 := by
  simp only [F, g]
  rw [max_eq_left (min_le_of_right_le (by linarith)), mul_zero]

/-- **Riemann sum**: `|Σ_{1 ≤ i ≤ N} F(i) - (11/54)h³| ≤ 16h²` for `2h ≤ N ≤ 2h + 2`, `h ≥ 1`. -/
theorem riemann {h : ℝ} (hh : 1 ≤ h) {N : ℕ} (hN : 2 * h ≤ N) (hN' : (N : ℝ) ≤ 2 * h + 2) :
    |∑ i ∈ Finset.Icc 1 N, F h i - 11 / 54 * h ^ 3| ≤ 16 * h ^ 2 := by
  have hc := F_cont h
  have hint : ∫ t in (0 : ℝ)..N, F h t = 11 / 54 * h ^ 3 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (2 * h))
      (hc.intervalIntegrable (2 * h) N), integral_F (by linarith)]
    have : ∫ t in (2 * h)..(N : ℝ), F h t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
        rw [Set.uIcc_of_le hN] at ht
        exact F_zero ht.1]
      simp
    rw [this, add_zero]
  have hsum : ∑ i ∈ Finset.Icc 1 N, F h i = ∑ k ∈ Finset.range N, F h ((k : ℝ) + 1) := by
    refine Finset.sum_nbij' (fun i => i - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; dsimp only; omega
    · intro k _; simp
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      congr 1
      rw [Nat.cast_sub hi.1]; push_cast; ring
  have hadj : ∑ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), F h t =
      ∫ t in ((0 : ℕ) : ℝ)..(N : ℝ), F h t :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hc.intervalIntegrable _ _
  rw [← hint, hsum]
  push_cast at hadj
  rw [← hadj, ← Finset.sum_sub_distrib]
  have hLip : ∀ k ∈ Finset.range N,
      |F h ((k : ℝ) + 1) - ∫ t in (k : ℝ)..(k + 1), F h t| ≤ h / 4 + 3 / 4 * N := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by
      have := Finset.mem_range.mp hk; exact_mod_cast this
    have e : F h ((k : ℝ) + 1) = ∫ _t in (k : ℝ)..(k + 1), F h ((k : ℝ) + 1) := by simp
    rw [e, ← intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ)) (b := k + 1)
      (C := h / 4 + 3 / 4 * N) (f := fun t => F h ((k : ℝ) + 1) - F h t) (fun t ht => by
        rw [Set.uIoc_of_le (by linarith)] at ht
        rw [Real.norm_eq_abs, abs_sub_comm]
        have := F_lip (h := h) (R := N) (t := t) (s := (k : ℝ) + 1) (by linarith) (by positivity) hkN
        refine this.trans ?_
        have : |t - ((k : ℝ) + 1)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        have hpos : 0 ≤ h / 4 + 3 / 4 * (N : ℝ) := by positivity
        nlinarith)
    rw [Real.norm_eq_abs, show (k : ℝ) + 1 - k = 1 by ring, abs_one, mul_one] at this
    exact this
  calc |∑ k ∈ Finset.range N, (F h ((k : ℝ) + 1) - ∫ t in (k : ℝ)..(k + 1), F h t)|
      ≤ ∑ k ∈ Finset.range N, |F h ((k : ℝ) + 1) - ∫ t in (k : ℝ)..(k + 1), F h t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, (h / 4 + 3 / 4 * (N : ℝ)) := Finset.sum_le_sum hLip
    _ = N * (h / 4 + 3 / 4 * N) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 16 * h ^ 2 := by nlinarith

end Cubic.BoxAsymptotic.MainIntegral
