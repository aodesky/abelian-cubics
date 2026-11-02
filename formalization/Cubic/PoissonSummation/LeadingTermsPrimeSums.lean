import Cubic.PoissonSummation.LeadingTermsLocalDerivatives
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Absolute convergence of the prime sums in `prop:leadingTerms`

Use mathlib's absolute convergence theorem for differentiated Dirichlet
series to obtain the summable majorant `log p / p²`. The explicit local
logarithmic derivatives are bounded by multiples of that majorant.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsPrimeSums

open FiniteEulerProduct LeadingTermsData

theorem prime_ge_two (p : Nat.Primes) : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast p.2.two_le

theorem prime_log_nonneg (p : Nat.Primes) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by linarith [prime_ge_two p])

theorem summable_prime_log : Summable (fun p : Nat.Primes =>
    Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have h := LSeriesSummable_logMul_of_lt_re (f := 1) (s := 2)
    (by rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have hp := h.norm.subtype Nat.Prime
  apply hp.congr
  intro p
  simp [LSeries.term_of_ne_zero p.2.ne_zero, LSeries.logMul, ← Complex.natCast_log,
    norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (prime_log_nonneg p)]

theorem inert_log_bound (p : Nat.Primes) :
    Real.log (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤
      2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp := prime_ge_two p
  have hlog := prime_log_nonneg p
  have hsq : 0 < (p : ℝ) ^ 2 := by positivity
  have hd : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  rw [← mul_div_assoc (2 : ℝ), div_le_div_iff₀ hd hsq]
  nlinarith [mul_nonneg hlog (show 0 ≤ (p : ℝ) ^ 2 - 2 by nlinarith)]

theorem summable_inert_log : Summable (fun q : InertPrimes =>
    ‖(Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1)‖) := by
  apply ((summable_prime_log.subtype (fun p => (p : ℕ) % 3 = 2)).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro q
  have hc : (Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1) =
      ((Real.log (q.1 : ℝ) / ((q.1 : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact inert_log_bound q.1
  · exact div_nonneg (prime_log_nonneg q.1) (by nlinarith [prime_ge_two q.1])

theorem split_log_bound (p : Nat.Primes) :
    ((2 * (p : ℝ) + 1) * Real.log (p : ℝ)) /
      (((p : ℝ) ^ 2 - 1) * ((p : ℝ) + 2)) ≤
      2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp := prime_ge_two p
  have hlog := prime_log_nonneg p
  have hsq : 0 < (p : ℝ) ^ 2 := by positivity
  have hd : 0 < ((p : ℝ) ^ 2 - 1) * ((p : ℝ) + 2) :=
    mul_pos (by nlinarith) (by positivity)
  rw [← mul_div_assoc (2 : ℝ), div_le_div_iff₀ hd hsq]
  have ht : 0 ≤ 3 * (p : ℝ) ^ 2 - 2 * (p : ℝ) - 4 := by nlinarith
  nlinarith [mul_nonneg hlog ht]

theorem summable_split_log : Summable (fun p : SplitPrimes => ‖splitLogTerm p‖) := by
  apply ((summable_prime_log.subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  have hc : splitLogTerm p =
      ((((2 * (p.1 : ℝ) + 1) * Real.log (p.1 : ℝ)) /
        (((p.1 : ℝ) ^ 2 - 1) * ((p.1 : ℝ) + 2)) : ℝ) : ℂ) := by
    simp [splitLogTerm]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact split_log_bound p.1
  · apply div_nonneg (mul_nonneg (by positivity) (prime_log_nonneg p.1))
    exact mul_nonneg (by nlinarith [prime_ge_two p.1]) (by positivity)

theorem original_split_log_bound (p : Nat.Primes) :
    3 * Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) + 2)) ≤
      3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp := prime_ge_two p
  have hlog := prime_log_nonneg p
  have hsq : 0 < (p : ℝ) ^ 2 := by positivity
  have hd : 0 < ((p : ℝ) - 1) * ((p : ℝ) + 2) := mul_pos (by linarith) (by positivity)
  rw [← mul_div_assoc (3 : ℝ), div_le_div_iff₀ hd hsq]
  nlinarith [mul_nonneg hlog (show 0 ≤ (p : ℝ) - 2 by linarith)]

theorem summable_original_split_log : Summable (fun p : SplitPrimes =>
    ‖3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
      ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2)‖) := by
  apply ((summable_prime_log.subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 3).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  have hc : 3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
      ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2) =
      ((3 * Real.log (p.1 : ℝ) / (((p.1 : ℝ) - 1) * ((p.1 : ℝ) + 2)) : ℝ) : ℂ) := by
    push_cast
    have hf : (p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2 =
        ((p.1 : ℂ) - 1) ^ 2 * ((p.1 : ℂ) + 2) := by ring
    rw [hf]
    field_simp [LeadingTermsLocalDerivatives.prime_sub_one_ne_zero p.1,
      LeadingTermsLocalDerivatives.prime_add_two_ne_zero p.1]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact original_split_log_bound p.1
  · apply div_nonneg (mul_nonneg (by norm_num) (prime_log_nonneg p.1))
    exact mul_nonneg (by linarith [prime_ge_two p.1]) (by positivity)

end Cubic.PoissonSummation.LeadingTermsPrimeSums
