import Cubic.BoxHeight.ConductorSumEuler
import Cubic.BoxHeight.ConductorSumHarmonic
import Cubic.BoxHeight.ConductorSumLValue

/-!
# Mean values of the conductor weight `g`

Let `g(m) = 2^{ω(m)}` for squarefree `m` all of whose prime factors are `≡ 1 (mod 3)`, and
`g(m) = 0` otherwise. We prove
* `Σ_{m ≤ x} g(m)/m ≥ A₀ log x - B` for `x ≥ 1`, with
  `A₀ = (2/3) (π/(3√3)) ∏_{q ≡ 2 (3)} (1 - q^{-2}) ∏_{p ≡ 1 (3)} (1 - 3p^{-2} + 2p^{-3})`;
* `Σ_{m ≤ x} g(m) ≤ B x` for `x ≥ 1`.

Write `g = h * b` with `b = χ * 1` (`ConductorSumData`), where `Σ |h(d)|/d` and
`Σ |h(d)| log d / d` converge and `Σ h(d)/d = (2/3) R(1)` (`ConductorSumEuler`). Then
`Σ_{m ≤ N} g(m)/m = Σ_{d ≤ N} (h(d)/d) T(⌊N/d⌋)` with `T(M) = Σ_{n ≤ M} b(n)/n`, and
`T(⌊N/d⌋) = L₁ (log N - log d) + O(1)` (`ConductorSumHarmonic`), where `L₁ = π/(3√3)`
(`ConductorSumLValue`). Hence
`Σ_{m ≤ N} g(m)/m = L₁ log N Σ_d h(d)/d - L₁ Σ_{d ≤ N} h(d) log d / d + O(1)`, and the tail
`log N · Σ_{d > N} h(d)/d` is at most `Σ_{d > N} |h(d)| log d / d`. This gives the two-sided
estimate `Σ_{m ≤ N} g(m)/m = A₀ log N + O(1)`.

For the count, `Σ_{m ≤ N} g(m) = Σ_{d ≤ N} h(d) Σ_{n ≤ N/d} b(n)`, and
`0 ≤ Σ_{n ≤ M} b(n) = Σ_{d ≤ M} χ(d) ⌊M/d⌋ ≤ M`, so `Σ_{m ≤ N} g(m) ≤ N Σ_d |h(d)|/d`.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open ArithmeticFunction Finset
open Cubic.Counting Cubic.PoissonSummation.FiniteEulerProduct

theorem gA_eq_mul' : gA = h * b := by rw [gA_eq_mul, mul_comm]

theorem Icc_one_eq_Ioc (N : ℕ) : Icc 1 N = Ioc 0 N := by ext; simp; omega

theorem sum_Ioc_eq_sum_range (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ range (N + 1), f d := by
  induction N with
  | zero => simp [hf]
  | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le N), ih, sum_range_succ _ (N + 1)]

/-! ### The logarithmic mean -/

/-- `Σ_{m ≤ N} g(m)/m = Σ_{d ≤ N} (h(d)/d) T(⌊N/d⌋)`. -/
theorem sum_g_div_eq (N : ℕ) :
    ∑ m ∈ Ioc 0 N, g m / m = ∑ d ∈ Ioc 0 N, hDiv d * Tsum (N / d) := by
  have hc := sum_Ioc_mul_eq_sum_sum (pdiv h) (pdiv b) N
  rw [← pdiv_mul, ← gA_eq_mul'] at hc
  simpa [pdiv_apply, Tsum, hDiv] using hc

theorem A₀_eq : A₀ = L₁ * ∑' d : ℕ, hDiv d := by
  rw [tsum_hDiv, L₁_eq, A₀]; ring

theorem summable_hDiv : Summable hDiv := summable_norm_hDiv.of_norm

theorem abs_hDiv (d : ℕ) : |hDiv d| = |h d| / d := by
  rw [hDiv, abs_div, Nat.abs_cast]

/-- `log N · |Σ_{d > N} h(d)/d| ≤ Σ_d |h(d)| log d / d`. -/
theorem abs_log_mul_tail_le (N : ℕ) :
    |Real.log N * ((∑' d : ℕ, hDiv d) - ∑ d ∈ Ioc 0 N, hDiv d)| ≤
      ∑' d : ℕ, |h d| * Real.log d / d := by
  have hv0 : ∀ d : ℕ, 0 ≤ |h d| * Real.log d / d := fun d => by
    have := Real.log_natCast_nonneg d; positivity
  have hsplit := summable_hDiv.sum_add_tsum_nat_add (N + 1)
  rw [← sum_Ioc_eq_sum_range hDiv (by simp [hDiv]) N] at hsplit
  have htail : (∑' d : ℕ, hDiv d) - ∑ d ∈ Ioc 0 N, hDiv d = ∑' k : ℕ, hDiv (k + (N + 1)) := by
    rw [← hsplit]; ring
  rw [htail]
  have habs : Summable (fun k : ℕ => ‖hDiv (k + (N + 1))‖) :=
    summable_norm_hDiv.comp_injective (add_left_injective (N + 1))
  have hvt : Summable (fun k : ℕ =>
      |h (k + (N + 1))| * Real.log ((k + (N + 1) : ℕ) : ℝ) / ((k + (N + 1) : ℕ) : ℝ)) :=
    summable_abs_h_log.comp_injective (add_left_injective (N + 1))
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hpt : ∀ k : ℕ, Real.log N * ‖hDiv (k + (N + 1))‖ ≤
      |h (k + (N + 1))| * Real.log ((k + (N + 1) : ℕ) : ℝ) / ((k + (N + 1) : ℕ) : ℝ) := by
    intro k
    rw [Real.norm_eq_abs, abs_hDiv]
    have hk : (0 : ℝ) < ((k + (N + 1) : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc', mul_comm (Real.log N)]
    apply div_le_div_of_nonneg_right _ hk.le
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using Real.log_natCast_nonneg (k + 1)
    · exact Real.log_le_log (by exact_mod_cast hN) (by push_cast; linarith)
  have hfin := sum_nonneg (s := range (N + 1)) (fun d _ => hv0 d)
  have hwhole := summable_abs_h_log.sum_add_tsum_nat_add (N + 1)
  rw [abs_mul, abs_of_nonneg hlog0]
  calc Real.log N * |∑' k : ℕ, hDiv (k + (N + 1))|
      ≤ Real.log N * ∑' k : ℕ, ‖hDiv (k + (N + 1))‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm habs) hlog0
    _ = ∑' k : ℕ, Real.log N * ‖hDiv (k + (N + 1))‖ := tsum_mul_left.symm
    _ ≤ ∑' k : ℕ, |h (k + (N + 1))| * Real.log ((k + (N + 1) : ℕ) : ℝ) /
          ((k + (N + 1) : ℕ) : ℝ) := (habs.mul_left _).tsum_le_tsum hpt hvt
    _ ≤ ∑' d : ℕ, |h d| * Real.log d / d := by linarith

/-- The two-sided estimate `|Σ_{m ≤ N} g(m)/m - A₀ log N| ≤ C`. -/
theorem abs_sum_g_div_sub_le (N : ℕ) :
    |∑ m ∈ Ioc 0 N, g m / m - A₀ * Real.log N| ≤
      |L₁| * (2 * ∑' d : ℕ, |h d| * Real.log d / d) +
        (6 + |L₁|) * ∑' d : ℕ, |h d| / d := by
  set Hs := ∑' d : ℕ, hDiv d
  set P := ∑ d ∈ Ioc 0 N, hDiv d
  set Q := ∑ d ∈ Ioc 0 N, hDiv d * Real.log d
  set E := ∑ d ∈ Ioc 0 N, hDiv d * (Tsum (N / d) - L₁ * (Real.log N - Real.log d))
  have hdec : ∑ m ∈ Ioc 0 N, g m / m - A₀ * Real.log N =
      -(L₁ * (Real.log N * (Hs - P))) - L₁ * Q + E := by
    have hG : ∑ d ∈ Ioc 0 N, hDiv d * Tsum (N / d) = L₁ * Real.log N * P - L₁ * Q + E := by
      simp only [P, Q, E, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun d _ => ?_
      ring
    rw [sum_g_div_eq, hG, A₀_eq]
    ring
  have hQ : |Q| ≤ ∑' d : ℕ, |h d| * Real.log d / d := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ d ∈ Ioc 0 N, |hDiv d * Real.log d| = |h d| * Real.log d / d := fun d _ => by
      rw [abs_mul, abs_hDiv, abs_of_nonneg (Real.log_natCast_nonneg d)]; ring
    rw [sum_congr rfl hle]
    exact summable_abs_h_log.sum_le_tsum _ (fun d _ => by
      have := Real.log_natCast_nonneg d; positivity)
  have hE : |E| ≤ (6 + |L₁|) * ∑' d : ℕ, |h d| / d := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ d ∈ Ioc 0 N,
        |hDiv d * (Tsum (N / d) - L₁ * (Real.log N - Real.log d))| ≤ (6 + |L₁|) * (|h d| / d) :=
      fun d hd => by
        simp only [mem_Ioc] at hd
        rw [abs_mul, abs_hDiv, mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_Tsum_div_sub_le hd.1 hd.2) (by positivity)
    refine (sum_le_sum hle).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (summable_abs_h_div.sum_le_tsum _
      (fun d _ => by positivity)) (by positivity)
  have htail := abs_log_mul_tail_le N
  rw [hdec]
  calc |-(L₁ * (Real.log N * (Hs - P))) - L₁ * Q + E|
      ≤ |L₁ * (Real.log N * (Hs - P))| + |L₁ * Q| + |E| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ = |L₁| * |Real.log N * (Hs - P)| + |L₁| * |Q| + |E| := by
        rw [abs_mul L₁ (Real.log N * (Hs - P)), abs_mul L₁ Q]
    _ ≤ |L₁| * (∑' d : ℕ, |h d| * Real.log d / d) + |L₁| * (∑' d : ℕ, |h d| * Real.log d / d) +
          (6 + |L₁|) * ∑' d : ℕ, |h d| / d := by gcongr
    _ = _ := by ring

theorem log_lower : ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x →
    A₀ * Real.log x - B ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, g m / m := by
  refine ⟨|L₁| * (2 * ∑' d : ℕ, |h d| * Real.log d / d) +
    (6 + |L₁|) * (∑' d : ℕ, |h d| / d) + |A₀|, fun x hx => ?_⟩
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hlog : 0 ≤ Real.log x - Real.log N ∧ Real.log x - Real.log N ≤ 1 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    constructor
    · exact Real.log_nonneg ((one_le_div (by linarith)).mpr hNx)
    · have := Real.log_le_sub_one_of_pos (show 0 < x / N by positivity)
      have : x / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  have hA : A₀ * Real.log x ≤ A₀ * Real.log N + |A₀| := by
    have : A₀ * (Real.log x - Real.log N) ≤ |A₀| * 1 := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_of_nonneg hlog.1]
      exact mul_le_mul_of_nonneg_left hlog.2 (abs_nonneg _)
    linarith
  have hmain := abs_sum_g_div_sub_le N
  rw [Icc_one_eq_Ioc]
  have := (abs_le.mp hmain).1
  linarith

/-! ### The count -/

/-- `0 ≤ Σ_{n ≤ M} b(n) ≤ M`. -/
theorem sum_b_bounds (M : ℕ) : 0 ≤ ∑ n ∈ Ioc 0 M, b n ∧ ∑ n ∈ Ioc 0 M, b n ≤ M := by
  have h := sum_Ioc_mul_zeta_eq_sum chiA M
  rw [← b] at h
  simp only [chiA_apply] at h
  rw [h]
  exact chi_floor_bounds M

theorem count_upper : ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x →
    ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, g m ≤ B * x := by
  refine ⟨∑' d : ℕ, |h d| / d, fun x hx => ?_⟩
  set N := ⌊x⌋₊
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hS0 : 0 ≤ ∑' d : ℕ, |h d| / d := tsum_nonneg fun d => by positivity
  have hc := sum_Ioc_mul_eq_sum_sum h b N
  rw [← gA_eq_mul'] at hc
  simp only [gA_apply] at hc
  rw [Icc_one_eq_Ioc, hc]
  have hle : ∀ d ∈ Ioc 0 N, h d * ∑ n ∈ Ioc 0 (N / d), b n ≤ N * (|h d| / d) := by
    intro d hd
    simp only [mem_Ioc] at hd
    obtain ⟨hb0, hb1⟩ := sum_b_bounds (N / d)
    have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    calc h d * ∑ n ∈ Ioc 0 (N / d), b n ≤ |h d| * ∑ n ∈ Ioc 0 (N / d), b n :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hb0
      _ ≤ |h d| * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left (hb1.trans hdiv) (abs_nonneg _)
      _ = N * (|h d| / d) := by ring
  refine (sum_le_sum hle).trans ?_
  rw [← mul_sum, mul_comm]
  refine (mul_le_mul_of_nonneg_right (summable_abs_h_div.sum_le_tsum _
    (fun d _ => by positivity)) (Nat.cast_nonneg N)).trans ?_
  exact mul_le_mul_of_nonneg_left hNx hS0

end Cubic.BoxHeight.ConductorSum
