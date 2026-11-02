import Cubic.BoxHeight.ConductorSumData
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Partial sums twisted by the character mod 3

The partial sums `A(N) = Σ_{d ≤ N} χ(d)` take only the values `0` and `1`. By summation by
parts, for `f` nonnegative and nonincreasing on `(M, ∞)`,
`|Σ_{M < d ≤ N} χ(d) f(d)| ≤ f(M + 1)`, and for `M = 0` the sum lies in `[0, f(1)]`.
We apply this to
* `f(d) = 1/d`: the partial sums `S(N) = Σ_{d ≤ N} χ(d)/d` satisfy `|S(N) - L₁| ≤ 1/(N+1)`,
  where `L₁ = Σ_{k ≥ 0} (1/(3k+1) - 1/(3k+2))`;
* `f(d) = log d / d` (nonincreasing for `d ≥ 3 > e`): `Σ_{d ≤ N} χ(d) log d / d` is bounded;
* `f(d) = ⌊M/d⌋`: `0 ≤ Σ_{d ≤ M} χ(d) ⌊M/d⌋ ≤ M`.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open Finset Filter
open scoped Topology

/-- `A(N) = Σ_{0 < d ≤ N} χ(d)`. -/
def chiSum (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N, chi d

theorem chiSum_succ (N : ℕ) : chiSum (N + 1) = chiSum N + chi (N + 1) :=
  sum_Ioc_succ_top (Nat.zero_le N) chi

theorem chiSum_eq (N : ℕ) : chiSum N = if N % 3 = 1 then 1 else 0 := by
  induction N with
  | zero => simp [chiSum]
  | succ N ih =>
    rw [chiSum_succ, ih]
    rcases mod_three_cases N with h | h | h <;>
      simp [chi, h, Nat.add_mod]

theorem chiSum_nonneg (N : ℕ) : 0 ≤ chiSum N := by
  rw [chiSum_eq]; split_ifs <;> norm_num

theorem chiSum_le_one (N : ℕ) : chiSum N ≤ 1 := by
  rw [chiSum_eq]; split_ifs <;> norm_num

/-- Summation by parts, as an invariant in `N`. -/
theorem abel_invariant (f : ℕ → ℝ) (M : ℕ) (hanti : ∀ d, M < d → f (d + 1) ≤ f d) :
    ∀ N, M ≤ N →
      -(chiSum M * f (M + 1)) ≤ (∑ d ∈ Ioc M N, chi d * f d) - chiSum N * f (N + 1) ∧
      (∑ d ∈ Ioc M N, chi d * f d) - chiSum N * f (N + 1) + f (N + 1) ≤
        (1 - chiSum M) * f (M + 1) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp; ring_nf; exact le_rfl
  | succ N hMN ih =>
    rw [sum_Ioc_succ_top hMN, chiSum_succ]
    have hf := hanti (N + 1) (by omega)
    have hA0 := chiSum_nonneg (N + 1)
    have hA1 := chiSum_le_one (N + 1)
    rw [chiSum_succ] at hA0 hA1
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hf)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hf)]

/-- `|Σ_{M < d ≤ N} χ(d) f(d)| ≤ f(M+1)` for `f` nonnegative and nonincreasing on `(M, ∞)`. -/
theorem abel_bounds (f : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (hanti : ∀ d, M < d → f (d + 1) ≤ f d) (hnn : ∀ d, M < d → 0 ≤ f d) :
    -(chiSum M * f (M + 1)) ≤ ∑ d ∈ Ioc M N, chi d * f d ∧
      ∑ d ∈ Ioc M N, chi d * f d ≤ (1 - chiSum M) * f (M + 1) := by
  obtain ⟨h1, h2⟩ := abel_invariant f M hanti N hMN
  have hN0 := chiSum_nonneg N
  have hN1 := chiSum_le_one N
  have hf := hnn (N + 1) (by omega)
  constructor
  · nlinarith [mul_nonneg hN0 hf]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hN1) hf]

theorem abs_abel_le (f : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (hanti : ∀ d, M < d → f (d + 1) ≤ f d) (hnn : ∀ d, M < d → 0 ≤ f d) :
    |∑ d ∈ Ioc M N, chi d * f d| ≤ f (M + 1) := by
  obtain ⟨h1, h2⟩ := abel_bounds f M N hMN hanti hnn
  have hf := hnn (M + 1) (by omega)
  have hA0 := chiSum_nonneg M
  have hA1 := chiSum_le_one M
  rw [abs_le]
  constructor <;> nlinarith

theorem abel_zero_bounds (f : ℕ → ℝ) (N : ℕ)
    (hanti : ∀ d, 0 < d → f (d + 1) ≤ f d) (hnn : ∀ d, 0 < d → 0 ≤ f d) :
    0 ≤ ∑ d ∈ Ioc 0 N, chi d * f d ∧ ∑ d ∈ Ioc 0 N, chi d * f d ≤ f 1 := by
  have h := abel_bounds f 0 N (Nat.zero_le N) hanti hnn
  simpa [chiSum] using h

/-! ### `f(d) = 1/d` -/

/-- `S(N) = Σ_{d ≤ N} χ(d)/d`. -/
def chiRecip (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ))

theorem recip_anti : ∀ d : ℕ, 0 < d → 1 / ((d + 1 : ℕ) : ℝ) ≤ 1 / (d : ℝ) := by
  intro d hd
  have : (0 : ℝ) < d := by exact_mod_cast hd
  apply one_div_le_one_div_of_le this
  push_cast; linarith

theorem chiRecip_bounds (N : ℕ) : 0 ≤ chiRecip N ∧ chiRecip N ≤ 1 := by
  have h := abel_zero_bounds (fun d : ℕ => 1 / (d : ℝ)) N recip_anti
    (fun d _ => by positivity)
  simpa [chiRecip] using h

theorem abs_chiRecip_sub_le {N N' : ℕ} (hN : N ≤ N') :
    |chiRecip N' - chiRecip N| ≤ 1 / ((N : ℝ) + 1) := by
  have h := abs_abel_le (fun d : ℕ => 1 / (d : ℝ)) N N' hN
    (fun d hd => recip_anti d (by omega)) (fun d _ => by positivity)
  rw [chiRecip, chiRecip, ← sum_Ioc_consecutive _ (Nat.zero_le N) hN, add_sub_cancel_left]
  simpa using h

/-- `L₁ = Σ_{k ≥ 0} (1/(3k+1) - 1/(3k+2))`. -/
def L₁ : ℝ := ∑' k : ℕ, (1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2))

theorem L_term_nonneg (k : ℕ) : 0 ≤ 1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2) := by
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

theorem L_term_le (k : ℕ) :
    1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem L_summable : Summable (fun k : ℕ => 1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2)) := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
      (Nat.succ_injective)
    simpa [Function.comp_def] using this
  exact hs.of_nonneg_of_le L_term_nonneg L_term_le

theorem chiRecip_three_mul (K : ℕ) : chiRecip (3 * K) =
    ∑ k ∈ range K, (1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2)) := by
  induction K with
  | zero => simp [chiRecip]
  | succ K ih =>
    rw [sum_range_succ, ← ih, chiRecip, chiRecip, show 3 * (K + 1) = 3 * K + 1 + 1 + 1 by ring,
      sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
    have h1 : (3 * K + 1) % 3 = 1 := by omega
    have h2 : (3 * K + 1 + 1) % 3 = 2 := by omega
    have h3 : (3 * K + 1 + 1 + 1) % 3 = 0 := by omega
    simp only [chi, h1, h2, h3]
    push_cast
    ring_nf

theorem tendsto_chiRecip_three_mul :
    Tendsto (fun K : ℕ => chiRecip (3 * K)) atTop (𝓝 L₁) := by
  simp only [chiRecip_three_mul]
  exact L_summable.hasSum.tendsto_sum_nat

/-- `|S(N) - L₁| ≤ 1/(N+1)`. -/
theorem abs_chiRecip_sub_L₁ (N : ℕ) : |chiRecip N - L₁| ≤ 1 / ((N : ℝ) + 1) := by
  have hlim : Tendsto (fun K : ℕ => |chiRecip (3 * K) - chiRecip N|) atTop
      (𝓝 |L₁ - chiRecip N|) :=
    (tendsto_chiRecip_three_mul.sub_const _).abs
  rw [abs_sub_comm]
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with K hK
  exact abs_chiRecip_sub_le (by omega)

/-! ### `f(d) = log d / d` -/

/-- `Σ_{d ≤ N} χ(d) log d / d`. -/
def chiLog (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N, chi d * (Real.log d / d)

theorem logDiv_anti (d : ℕ) (hd : 2 < d) :
    Real.log ((d + 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ) ≤ Real.log d / d := by
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.log_div_self_antitoneOn
  · show Real.exp 1 ≤ (d : ℝ); linarith
  · show Real.exp 1 ≤ ((d + 1 : ℕ) : ℝ); push_cast; linarith
  · push_cast; linarith

theorem abs_chiLog_le (N : ℕ) : |chiLog N| ≤ 2 := by
  rcases lt_or_ge N 2 with hN | hN
  · have hz : chiLog N = 0 := by
      refine sum_eq_zero fun d hd => ?_
      have : d = 1 := by simp at hd; omega
      simp [this]
    rw [hz]; norm_num
  have hsplit : chiLog N = chiLog 2 + ∑ d ∈ Ioc 2 N, chi d * (Real.log d / d) := by
    rw [chiLog, chiLog, sum_Ioc_consecutive _ (by norm_num) hN]
  have h2 : chiLog 2 = -(Real.log 2 / 2) := by
    rw [chiLog, show (2 : ℕ) = 0 + 1 + 1 from rfl, sum_Ioc_succ_top (by norm_num),
      sum_Ioc_succ_top (by norm_num)]
    simp [chi]
  have htail := abs_abel_le (fun d : ℕ => Real.log d / d) 2 N hN logDiv_anti
    (fun d _ => by have := Real.log_natCast_nonneg d; positivity)
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simp only at htail
  rw [hsplit, h2]
  have : |Real.log ((2 + 1 : ℕ) : ℝ) / ((2 + 1 : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_le]; push_cast
    constructor
    · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); linarith
    · linarith
  calc |-(Real.log 2 / 2) + ∑ d ∈ Ioc 2 N, chi d * (Real.log d / d)|
      ≤ |-(Real.log 2 / 2)| + |∑ d ∈ Ioc 2 N, chi d * (Real.log d / d)| := abs_add_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · rw [abs_neg, abs_of_nonneg (by positivity)]; linarith
        · exact htail.trans (le_abs_self _ |>.trans this)
    _ = 2 := by norm_num

/-! ### `f(d) = ⌊M/d⌋` -/

theorem chi_floor_bounds (M : ℕ) :
    0 ≤ ∑ d ∈ Ioc 0 M, chi d * ((M / d : ℕ) : ℝ) ∧
      ∑ d ∈ Ioc 0 M, chi d * ((M / d : ℕ) : ℝ) ≤ M := by
  have h := abel_zero_bounds (fun d : ℕ => ((M / d : ℕ) : ℝ)) M
    (fun d hd => by
      show ((M / (d + 1) : ℕ) : ℝ) ≤ ((M / d : ℕ) : ℝ)
      exact_mod_cast Nat.div_le_div_left (Nat.le_succ d) hd)
    (fun d _ => Nat.cast_nonneg _)
  simpa using h

end Cubic.BoxHeight.ConductorSum
