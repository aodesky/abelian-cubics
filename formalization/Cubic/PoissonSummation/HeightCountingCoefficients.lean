import Cubic.PoissonSummation.HeightCountingData
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Arithmetic coefficients with the exceptional prime removed

These are the coefficients proposed by the paper, not definitions of point
counts. The factor at three is one, so every positive power of three has
coefficient zero. Away from three they are the literal divisor sum. The
elementary quadratic bound below is only used to justify coefficient
comparison in a common right half-plane; it makes no sharp asymptotic claim.
-/

namespace Cubic.PoissonSummation.HeightCountingCoefficients

open ArithmeticFunction

def coefficient : ArithmeticFunction ℤ where
  toFun n := if 3 ∣ n then 0 else coefficientDivisorSum n
  map_zero' := by simp

theorem coefficient_apply (n : ℕ) :
    coefficient n = if 3 ∣ n then 0 else coefficientDivisorSum n := rfl

theorem away_three (n : ℕ) (hn : ¬ 3 ∣ n) :
    coefficient n = HeightCountingData.divisorFormula n := by
  rw [coefficient_apply, if_neg hn, coefficientDivisorSum_eq_paper_formula]
  rfl

theorem multiplicative : coefficient.IsMultiplicative := by
  constructor
  · simp [coefficient_apply, coefficientDivisorSum_multiplicative.1]
  · intro m n hmn
    simp only [coefficient_apply, Nat.prime_three.dvd_mul]
    by_cases hm : 3 ∣ m <;> by_cases hn : 3 ∣ n <;>
      simp [hm, hn, coefficientDivisorSum_multiplicative.2 hmn]

theorem prime_pow_away {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (k : ℕ) :
    coefficient (p ^ k) = coefficientDivisorSum (p ^ k) := by
  rw [coefficient_apply, if_neg]
  intro hd
  exact hp3 ((hp.dvd_iff_eq (by decide)).mp
    (Nat.prime_three.dvd_of_dvd_pow hd))

theorem three_pow_succ (k : ℕ) : coefficient (3 ^ (k + 1)) = 0 := by
  simp [coefficient_apply, pow_succ]

theorem split {p : ℕ} (hp : p.Prime) (hres : p % 3 = 1) (k : ℕ) :
    coefficient (p ^ k) = 3 * (k : ℤ) + 1 := by
  rw [prime_pow_away hp (by intro h; simp [h] at hres), coefficientDivisorSum_split hp hres]

theorem inert_even {p : ℕ} (hp : p.Prime) (hres : p % 3 = 2) (k : ℕ) :
    coefficient (p ^ (2 * k)) = 1 := by
  rw [prime_pow_away hp (by intro h; simp [h] at hres), coefficientDivisorSum_inert_even hp hres]

theorem inert_odd {p : ℕ} (hp : p.Prime) (hres : p % 3 = 2) (k : ℕ) :
    coefficient (p ^ (2 * k + 1)) = 0 := by
  rw [prime_pow_away hp (by intro h; simp [h] at hres), coefficientDivisorSum_inert_odd hp hres]

theorem weight_abs_le (p k : ℕ) : |primePowerWeight p k| ≤ 3 := by
  unfold primePowerWeight
  split_ifs <;> simp [abs_pow]

theorem divisor_sum_prime_pow_abs_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |coefficientDivisorSum (p ^ k)| ≤ 3 * (k : ℤ) + 1 := by
  induction k with
  | zero => simp [coefficientDivisorSum_multiplicative.1]
  | succ k ih =>
    rw [coefficientDivisorSum_prime_pow hp] at ih ⊢
    rw [Finset.sum_range_succ]
    have h := (abs_add_le _ _).trans (add_le_add ih (weight_abs_le p (k + 1)))
    push_cast
    linarith

theorem linear_le_prime_pow_sq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    3 * k + 1 ≤ (p ^ k) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp2 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
    have hx : 1 ≤ (p ^ k) ^ 2 := one_le_pow₀ (one_le_pow₀ hp.one_lt.le)
    rw [pow_succ p k, mul_pow]
    nlinarith

theorem divisor_sum_abs_le (n : ℕ) : |coefficientDivisorSum n| ≤ (n : ℤ) ^ 2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    exact (divisor_sum_prime_pow_abs_le hp k).trans (by
      exact_mod_cast linear_le_prime_pow_sq hp k)
  | coprime a b _ _ hab ha hb =>
    rw [coefficientDivisorSum_multiplicative.2 hab, abs_mul, Nat.cast_mul, mul_pow]
    exact mul_le_mul ha hb (abs_nonneg _) (sq_nonneg _)

theorem abs_le (n : ℕ) : |coefficient n| ≤ (n : ℤ) ^ 2 := by
  rw [coefficient_apply]
  split_ifs
  · simp
  · exact divisor_sum_abs_le n

theorem series_summable (s : ℂ) (hs : 3 < s.re) :
    LSeriesSummable (fun n => (coefficient n : ℂ)) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 3) hs
  refine ⟨1, fun n _ => ?_⟩
  norm_num only [one_mul, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  rw [Complex.norm_intCast]
  exact_mod_cast abs_le n

end Cubic.PoissonSummation.HeightCountingCoefficients
