import Cubic.BoxHeight.ConductorSumAlternating
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `Σ_{n ≤ N} b(n)/n = L₁ log N + O(1)`

Since `b = χ * 1`, swapping the order of summation gives
`T(N) = Σ_{n ≤ N} b(n)/n = Σ_{d ≤ N} (χ(d)/d) H(⌊N/d⌋)` with `H` the harmonic numbers.
Using `H(m) = log m + γ + O(1/m)` and `log ⌊N/d⌋ = log N - log d + O(d/N)`,
`T(N) = (log N + γ) S(N) - Σ_{d ≤ N} χ(d) log d / d + O(1)`, where `S(N) = Σ_{d ≤ N} χ(d)/d`.
Now `|S(N) - L₁| ≤ 1/(N+1)` and the twisted logarithmic sum is bounded
(`ConductorSumAlternating`), so `|T(N) - L₁ log N| ≤ 6`.

We also record the `1/n`-twisted form of Dirichlet convolution used to swap the summations.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open ArithmeticFunction Finset

/-! ### Dividing an arithmetic function by `n` -/

/-- `n ↦ f(n)/n`. -/
def pdiv (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun n => f n / n, by simp⟩

@[simp] theorem pdiv_apply (f : ArithmeticFunction ℝ) (n : ℕ) : pdiv f n = f n / n := rfl

/-- Division by `n` is compatible with Dirichlet convolution. -/
theorem pdiv_mul (f₁ f₂ : ArithmeticFunction ℝ) : pdiv (f₁ * f₂) = pdiv f₁ * pdiv f₂ := by
  ext n
  simp only [pdiv_apply, mul_apply, sum_div]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [← hx1, Nat.cast_mul, mul_div_mul_comm]

/-! ### Harmonic numbers -/

/-- `H(n) = Σ_{0 < e ≤ n} 1/e`. -/
def Hm (n : ℕ) : ℝ := ∑ e ∈ Ioc 0 n, 1 / (e : ℝ)

theorem Hm_eq_harmonic (n : ℕ) : Hm n = (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc, Hm, show Icc 1 n = Ioc 0 n by ext; simp; omega]
  push_cast
  simp

theorem Hm_sub_log_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ Hm n - Real.log n - Real.eulerMascheroniConstant ∧
      Hm n - Real.log n - Real.eulerMascheroniConstant ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq', if_neg hn.ne'] at h1
  rw [Real.eulerMascheroniSeq] at h2
  rw [← Hm_eq_harmonic] at h1 h2
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hn'.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
    have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  constructor <;> linarith

/-- `log ⌊N/d⌋ = log N - log d + O(1/⌊N/d⌋)`. -/
theorem log_div_floor_bounds {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    0 < N / d ∧ 0 ≤ Real.log N - Real.log d - Real.log ((N / d : ℕ) : ℝ) ∧
      Real.log N - Real.log d - Real.log ((N / d : ℕ) : ℝ) ≤ 1 / ((N / d : ℕ) : ℝ) ∧
      1 / ((N / d : ℕ) : ℝ) ≤ 2 * d / N := by
  have hm : 0 < N / d := Nat.div_pos hdN hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hdN
  set m := N / d with hmdef
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : (m : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  have hhi : (N : ℝ) < (m + 1) * d := by
    have := Nat.lt_div_mul_add (a := N) hd
    rw [← hmdef] at this
    exact_mod_cast (by nlinarith : N < (m + 1) * d)
  have hlog : Real.log N - Real.log d - Real.log m = Real.log (N / (m * d)) := by
    rw [Real.log_div hN'.ne' (by positivity), Real.log_mul hm'.ne' hd'.ne']; ring
  refine ⟨hm, ?_, ?_, ?_⟩
  · rw [hlog]
    exact Real.log_nonneg ((one_le_div (by positivity)).mpr hlo)
  · rw [hlog]
    have := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / (m * d) by positivity)
    have hq : (N : ℝ) / (m * d) - 1 ≤ 1 / m := by
      rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hm']
      nlinarith
    linarith
  · rw [div_le_div_iff₀ hm' hN']
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-! ### The sum `T(N)` -/

/-- `T(N) = Σ_{n ≤ N} b(n)/n`. -/
def Tsum (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, b n / n

theorem pdiv_zeta_apply {e : ℕ} (he : e ≠ 0) :
    pdiv ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) e = 1 / (e : ℝ) := by
  simp [natCoe_apply, zeta_apply_ne he]

theorem Tsum_eq (N : ℕ) : Tsum N = ∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * Hm (N / d) := by
  have h := sum_Ioc_mul_eq_sum_sum (pdiv chiA)
    (pdiv ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) N
  rw [← pdiv_mul, ← b] at h
  simp only [pdiv_apply] at h
  rw [Tsum, h]
  refine sum_congr rfl fun d _ => ?_
  rw [Hm, chiA_apply, div_eq_mul_one_div (chi d)]
  congr 1
  refine sum_congr rfl fun e he => ?_
  rw [← pdiv_apply, pdiv_zeta_apply (by simp at he; omega)]

/-- `|T(N) - L₁ log N| ≤ 6`. -/
theorem abs_Tsum_sub_le (N : ℕ) : |Tsum N - L₁ * Real.log N| ≤ 6 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Tsum]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set γ := Real.eulerMascheroniConstant
  -- the error terms `r_d`
  set r : ℕ → ℝ := fun d => Hm (N / d) - (Real.log N - Real.log d + γ) with hr
  have hr_le : ∀ d ∈ Ioc 0 N, |chi d * (1 / (d : ℝ)) * r d| ≤ 2 / N := by
    intro d hd
    simp only [mem_Ioc] at hd
    obtain ⟨hm, h1, h2, h3⟩ := log_div_floor_bounds hd.1 hd.2
    obtain ⟨h4, h5⟩ := Hm_sub_log_bounds hm
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hrd : |r d| ≤ 2 * d / N := by
      rw [abs_le]; simp only [hr]; constructor <;> linarith
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / d)]
    calc |chi d| * (1 / d) * |r d| ≤ 1 * (1 / d) * (2 * d / N) := by
          gcongr
          exact abs_chi_le d
      _ = 2 / N := by field_simp
  have hE : |∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * r d| ≤ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hr_le).trans ?_
    simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    field_simp
    exact le_rfl
  have hdecomp : Tsum N - L₁ * Real.log N =
      (∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * r d) + Real.log N * (chiRecip N - L₁) +
        γ * chiRecip N - chiLog N := by
    have key : ∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * Hm (N / d) =
        (∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * r d) +
          (Real.log N + γ) * (∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ))) -
          ∑ d ∈ Ioc 0 N, chi d * (Real.log d / d) := by
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => ?_
      simp only [hr]
      ring
    rw [Tsum_eq, key, chiRecip, chiLog]
    ring
  have hS := abs_chiRecip_sub_L₁ N
  obtain ⟨hS0, hS1⟩ := chiRecip_bounds N
  have hlogN : Real.log N ≤ N + 1 := by
    have := Real.log_le_sub_one_of_pos hN'; linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : |Real.log N * (chiRecip N - L₁)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlog0]
    calc Real.log N * |chiRecip N - L₁| ≤ (N + 1) * (1 / ((N : ℝ) + 1)) :=
          mul_le_mul hlogN hS (abs_nonneg _) (by positivity)
      _ = 1 := by field_simp
  have hγ0 : 0 ≤ γ := (Real.one_half_lt_eulerMascheroniConstant.le.trans' (by norm_num))
  have hγ1 : γ ≤ 1 := Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
  have h2 : |γ * chiRecip N| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hγ0 hS0)]; nlinarith
  have h3 := abs_chiLog_le N
  rw [hdecomp]
  calc |(∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * r d) + Real.log N * (chiRecip N - L₁) +
        γ * chiRecip N - chiLog N|
      ≤ |∑ d ∈ Ioc 0 N, chi d * (1 / (d : ℝ)) * r d| + |Real.log N * (chiRecip N - L₁)| +
        |γ * chiRecip N| + |chiLog N| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 2 + 1 + 1 + 2 := by gcongr
    _ = 6 := by norm_num

/-- `T(⌊N/d⌋) = L₁ (log N - log d) + O(1)` for `d ≤ N`. -/
theorem abs_Tsum_div_sub_le {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    |Tsum (N / d) - L₁ * (Real.log N - Real.log d)| ≤ 6 + |L₁| := by
  obtain ⟨hm, h1, h2, -⟩ := log_div_floor_bounds hd hdN
  have hm1 : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hm
  have hinv : 1 / ((N / d : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm1
  have hT := abs_Tsum_sub_le (N / d)
  have hdiff : |L₁ * Real.log ((N / d : ℕ) : ℝ) - L₁ * (Real.log N - Real.log d)| ≤ |L₁| := by
    rw [← mul_sub, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_le]; constructor <;> linarith
  calc |Tsum (N / d) - L₁ * (Real.log N - Real.log d)|
      = |(Tsum (N / d) - L₁ * Real.log ((N / d : ℕ) : ℝ)) +
          (L₁ * Real.log ((N / d : ℕ) : ℝ) - L₁ * (Real.log N - Real.log d))| := by ring_nf
    _ ≤ |Tsum (N / d) - L₁ * Real.log ((N / d : ℕ) : ℝ)| +
          |L₁ * Real.log ((N / d : ℕ) : ℝ) - L₁ * (Real.log N - Real.log d)| := abs_add_le _ _
    _ ≤ 6 + |L₁| := add_le_add hT hdiff

end Cubic.BoxHeight.ConductorSum
