import Cubic.PoissonSummation.LeadingTermsCorrection
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# Local logarithmic derivatives in the paper's variable `s`

These calculations retain the chain factor `1/2` in `z=s/2`. They concern
the actual local functions, not formally differentiated symbols. Passing
from the local identities to an infinite prime sum requires separate
convergence and nonvanishing proofs.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsLocalDerivatives

open FiniteEulerProduct

theorem prime_ne_zero (p : Nat.Primes) : (p : ℂ) ≠ 0 := by
  exact_mod_cast p.2.ne_zero

theorem prime_sub_one_ne_zero (p : Nat.Primes) : (p : ℂ) - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  exact_mod_cast p.2.ne_one

theorem prime_add_one_ne_zero (p : Nat.Primes) : (p : ℂ) + 1 ≠ 0 := by
  exact_mod_cast (show (p : ℝ) + 1 ≠ 0 by positivity)

theorem prime_add_two_ne_zero (p : Nat.Primes) : (p : ℂ) + 2 ≠ 0 := by
  exact_mod_cast (show (p : ℝ) + 2 ≠ 0 by positivity)

theorem prime_sq_sub_one_ne_zero (p : Nat.Primes) : (p : ℂ) ^ 2 - 1 ≠ 0 := by
  have h : (p : ℂ) ^ 2 - 1 = ((p : ℂ) - 1) * ((p : ℂ) + 1) := by ring
  rw [h]
  exact mul_ne_zero (prime_sub_one_ne_zero p) (prime_add_one_ne_zero p)

/-- The derivative of `p^(s/2)` at 2 includes exactly one chain factor `1/2`. -/
theorem power_half_derivative (p : Nat.Primes) : HasDerivAt
    (fun s : ℂ => (p : ℂ) ^ (s / 2))
    ((Real.log (p : ℝ) : ℂ) * (p : ℂ) / 2) 2 := by
  convert ((hasDerivAt_id (2 : ℂ)).div_const 2).const_cpow
    (c := (p : ℂ)) (.inl (prime_ne_zero p)) using 1
  simp [← Complex.natCast_log]
  ring

theorem inverse_power_half_derivative (p : Nat.Primes) : HasDerivAt
    (fun s : ℂ => (p : ℂ) ^ (-(s / 2)))
    (-(Real.log (p : ℝ) : ℂ) / (2 * (p : ℂ))) 2 := by
  convert (((hasDerivAt_id (2 : ℂ)).div_const 2).neg).const_cpow
    (c := (p : ℂ)) (.inl (prime_ne_zero p)) using 1
  simp [← Complex.natCast_log, Complex.cpow_neg]
  ring

theorem inert_log_derivative (q : InertPrimes) :
    logDeriv (fun s : ℂ => HeightZetaCorrectionProduct.inert q (s / 2)) 2 =
      (Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1) := by
  simp_rw [HeightZetaCorrectionProduct.inert, HeightZetaCorrectionProduct.primePower_two]
  have hd := (hasDerivAt_const (2 : ℂ) 1).sub
    ((inverse_power_half_derivative q.1).fun_pow 2)
  simp only [Pi.sub_def] at hd
  rw [logDeriv_apply, hd.deriv]
  simp only [div_self (by norm_num : (2 : ℂ) ≠ 0)]
  norm_num [Complex.cpow_neg]
  field_simp [prime_ne_zero q.1, prime_sq_sub_one_ne_zero q.1]

theorem split_log_derivative (p : SplitPrimes) :
    logDeriv (fun s : ℂ => HeightZetaCorrectionProduct.split p (s / 2)) 2 =
      3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
        ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2) := by
  have hn : (p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2 ≠ 0 := by
    have h : (p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2 =
        ((p.1 : ℂ) - 1) ^ 2 * ((p.1 : ℂ) + 2) := by ring
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ (prime_sub_one_ne_zero p.1)) (prime_add_two_ne_zero p.1)
  simp_rw [HeightZetaCorrectionProduct.split, HeightZetaCorrectionProduct.primePower_two,
    HeightZetaCorrectionProduct.primePower_three]
  have hd := ((hasDerivAt_const (2 : ℂ) 1).sub
    (((inverse_power_half_derivative p.1).fun_pow 2).const_mul 3)).add
    (((inverse_power_half_derivative p.1).fun_pow 3).const_mul 2)
  simp only [Pi.sub_def, Pi.add_def] at hd
  rw [logDeriv_apply, hd.deriv]
  norm_num [Complex.cpow_neg]
  field_simp [prime_ne_zero p.1, hn]
  ring

theorem simplified_split_log_derivative (p : SplitPrimes) :
    logDeriv (LeadingTermsData.splitFactor p) 2 = LeadingTermsData.splitLogTerm p := by
  have hden : (p.1 : ℂ) ^ (2 / 2 : ℂ) * ((p.1 : ℂ) ^ (2 / 2 : ℂ) + 1) ≠ 0 := by
    simpa using mul_ne_zero (prime_ne_zero p.1) (prime_add_one_ne_zero p.1)
  have hd := (hasDerivAt_const (2 : ℂ) 1).sub
    ((hasDerivAt_const (2 : ℂ) 2).div
      ((power_half_derivative p.1).mul ((power_half_derivative p.1).add_const 1)) hden)
  simp only [Pi.sub_def, Pi.div_def, Pi.mul_def] at hd
  change HasDerivAt (LeadingTermsData.splitFactor p) _ 2 at hd
  rw [logDeriv_apply, hd.deriv]
  norm_num [LeadingTermsData.splitLogTerm, LeadingTermsData.splitFactor]
  have hn : (p.1 : ℂ) * ((p.1 : ℂ) + 1) - 2 ≠ 0 := by
    have h : (p.1 : ℂ) * ((p.1 : ℂ) + 1) - 2 =
        ((p.1 : ℂ) - 1) * ((p.1 : ℂ) + 2) := by ring
    rw [h]
    exact mul_ne_zero (prime_sub_one_ne_zero p.1) (prime_add_two_ne_zero p.1)
  field_simp [prime_ne_zero p.1, prime_add_one_ne_zero p.1,
    prime_sq_sub_one_ne_zero p.1, prime_add_two_ne_zero p.1, hn]
  ring

/-- The original ramified factor contributes `log 3 / 2`. -/
theorem ramified_log_derivative :
    logDeriv (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2) 2 =
      (1 / 2 : ℂ) * (Real.log 3 : ℂ) := by
  have hd := ((hasDerivAt_const (2 : ℂ) 1).fun_sub
    (inverse_power_half_derivative ⟨3, Nat.prime_three⟩)).fun_pow 2
  norm_num only [Subtype.coe_mk, Nat.cast_ofNat] at hd
  rw [logDeriv_apply, hd.deriv]
  norm_num [Complex.cpow_neg]
  ring

/-- After extracting `1/ζ(s)`, the ramified quotient contributes `3 log 3 / 8`. -/
theorem ramified_quotient_log_derivative :
    logDeriv (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) /
      (1 + (3 : ℂ) ^ (-(s / 2)))) 2 = (3 / 8 : ℂ) * (Real.log 3 : ℂ) := by
  have hp := inverse_power_half_derivative ⟨3, Nat.prime_three⟩
  have hd := ((hasDerivAt_const (2 : ℂ) 1).fun_sub hp).fun_div
    ((hasDerivAt_const (2 : ℂ) 1).fun_add hp) (by norm_num [Complex.cpow_neg])
  norm_num only [Subtype.coe_mk, Nat.cast_ofNat] at hd
  rw [logDeriv_apply, hd.deriv]
  norm_num [Complex.cpow_neg]
  ring

end Cubic.PoissonSummation.LeadingTermsLocalDerivatives
