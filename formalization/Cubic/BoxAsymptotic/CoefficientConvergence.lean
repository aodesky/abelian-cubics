import Cubic.PoissonSummation.HeightCountingCoefficients
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Data.Nat.Choose.Sum

/-! Direct absolute convergence from the fourfold divisor function.  Its
prime-power coefficients dominate the split coefficients `3j+1`; the other
local coefficients are zero or one. No height-counting or Poisson theorem is
used in this comparison. -/

noncomputable section

namespace Cubic.BoxAsymptotic.CoefficientConvergence

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

def divisorPower (r : ℕ) : ArithmeticFunction ℕ := ζ ^ r

theorem divisorPower_multiplicative (r : ℕ) : (divisorPower r).IsMultiplicative := by
  induction r with
  | zero => simpa [divisorPower] using (isMultiplicative_one : (1 : ArithmeticFunction ℕ).IsMultiplicative)
  | succ r ih => simpa [divisorPower, pow_succ] using ih.mul isMultiplicative_zeta

theorem divisorPower_prime_pow {p : ℕ} (hp : p.Prime) (r j : ℕ) :
    divisorPower (r + 1) (p ^ j) = (j + r).choose r := by
  induction r generalizing j with
  | zero => simp [divisorPower, hp.ne_zero]
  | succ r ih =>
    change (ζ ^ (r + 1 + 1)) (p ^ j) = _
    rw [pow_succ, mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    change (∑ i ∈ Finset.range (j + 1), divisorPower (r + 1) (p ^ i)) = _
    simp only [ih]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.sum_range_add_choose j r

theorem linear_le_choose (j : ℕ) : 3 * j + 1 ≤ (j + 3).choose 3 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hb : 3 ≤ (j + 3).choose 2 :=
      (by decide : 3 ≤ (3 : ℕ).choose 2).trans (Nat.choose_le_choose 2 (by omega))
    have he : (j + 1 + 3).choose 3 = (j + 3).choose 2 + (j + 3).choose 3 := by
      convert Nat.choose_succ_succ (j + 3) 2 using 1
    rw [he]
    omega

theorem coefficient_le (n : ℕ) :
    |Cubic.PoissonSummation.HeightCountingCoefficients.coefficient n| ≤ (divisorPower 4 n : ℤ) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p j hp =>
    rw [divisorPower_prime_pow hp 3 j]
    by_cases h3 : 3 ∣ p ^ j
    · simp [Cubic.PoissonSummation.HeightCountingCoefficients.coefficient_apply, h3]
    · rw [Cubic.PoissonSummation.HeightCountingCoefficients.coefficient_apply, if_neg h3]
      exact (Cubic.PoissonSummation.HeightCountingCoefficients.divisor_sum_prime_pow_abs_le hp j).trans
        (by exact_mod_cast linear_le_choose j)
  | coprime a b _ _ hab ha hb =>
    rw [Cubic.PoissonSummation.HeightCountingCoefficients.multiplicative.2 hab,
      abs_mul, (divisorPower_multiplicative 4).2 hab, Nat.cast_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (by positivity)

theorem cast_power (r : ℕ) :
    ((divisorPower r : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) =
      (ζ : ArithmeticFunction ℂ) ^ r := by
  induction r with
  | zero => simp [divisorPower]
  | succ r ih =>
    simpa only [divisorPower, pow_succ, natCoe_mul] using congrArg (· * (ζ : ArithmeticFunction ℂ)) ih

theorem divisorPower_summable (r : ℕ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorPower (r + 1) n : ℂ)) s := by
  have hz : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s := by
    simpa only [natCoe_apply] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have h (r : ℕ) : LSeriesSummable (⇑((ζ : ArithmeticFunction ℂ) ^ (r + 1))) s := by
    induction r with
    | zero => simpa using hz
    | succ r ih =>
      rw [pow_succ]
      exact ArithmeticFunction.LSeriesSummable_mul ih hz
  simpa only [← cast_power, natCoe_apply] using h r

/-- The actual arithmetic coefficients converge on `Re s > 1`, by `d₄`. -/
theorem summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Cubic.PoissonSummation.HeightCountingCoefficients.coefficient n : ℂ)) s := by
  rw [LSeriesSummable, ← summable_norm_iff]
  apply (divisorPower_summable 3 s hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n =>
    LSeries.norm_term_le s ?_
  rw [Complex.norm_intCast, Complex.norm_natCast]
  exact_mod_cast coefficient_le n

end Cubic.BoxAsymptotic.CoefficientConvergence
