import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The divisor bound `τ(n) ≪_η n^η`

Used in the proof of `eqn:dSummatoryForGeneralTrace` in the form
`d_n ≤ τ(n)³ ≪_η n^η`. The argument is the usual one: `τ` is the product of
`k+1` over the prime powers `p^k ∥ n`; each factor is at most `M·p^{kη}`, and
at most `p^{kη}` once `p^η ≥ 2`, so only the primes below `2^{1/η}` contribute
the constant.
-/

namespace Cubic.Counting.DivisorBound

open Real

/-- `k+1 ≤ M·2^{kη}` with `M = max 1 (1/(η log 2))`. -/
theorem succ_le_const_mul_two_rpow {η : ℝ} (hη : 0 < η) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (η * Real.log 2)) * (2 : ℝ) ^ ((k : ℝ) * η) := by
  have hl : 0 < η * Real.log 2 := mul_pos hη (Real.log_pos one_lt_two)
  have hexp : 1 + (k : ℝ) * η * Real.log 2 ≤ (2 : ℝ) ^ ((k : ℝ) * η) := by
    rw [Real.rpow_def_of_pos two_pos]
    have := Real.add_one_le_exp (Real.log 2 * ((k : ℝ) * η))
    linarith [show Real.log 2 * ((k : ℝ) * η) = (k : ℝ) * η * Real.log 2 by ring]
  have hM : 1 ≤ max 1 (1 / (η * Real.log 2)) := le_max_left _ _
  have hM' : 1 / (η * Real.log 2) ≤ max 1 (1 / (η * Real.log 2)) := le_max_right _ _
  have hk : (k : ℝ) ≤ max 1 (1 / (η * Real.log 2)) * ((k : ℝ) * η * Real.log 2) := by
    have : (k : ℝ) = 1 / (η * Real.log 2) * ((k : ℝ) * η * Real.log 2) := by
      field_simp
    calc (k : ℝ) = 1 / (η * Real.log 2) * ((k : ℝ) * η * Real.log 2) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right hM' (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ max 1 (1 / (η * Real.log 2)))]

/-- One prime-power factor of `τ(n)`. -/
theorem prime_factor_le {η : ℝ} (hη : 0 < η) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((k : ℝ) + 1) ≤ (if (p : ℝ) < 2 ^ (1 / η) then max 1 (1 / (η * Real.log 2)) else 1) *
      (p : ℝ) ^ ((k : ℝ) * η) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs with h
  · calc ((k : ℝ) + 1) ≤ max 1 (1 / (η * Real.log 2)) * (2 : ℝ) ^ ((k : ℝ) * η) :=
          succ_le_const_mul_two_rpow hη k
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
  · push_neg at h
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ η := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h hη.le
    have hpow : (p : ℝ) ^ ((k : ℝ) * η) = ((p : ℝ) ^ η) ^ k := by
      rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
    have hbern : ((k : ℝ) + 1) ≤ 2 ^ k := by
      have := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) k
      norm_num at this
      linarith
    rw [one_mul, hpow]
    exact hbern.trans (pow_le_pow_left₀ (by norm_num) h2 k)

/-- The constant: `M` raised to the number of primes below `2^{1/η}`. -/
noncomputable def constant (η : ℝ) : ℝ :=
  max 1 (1 / (η * Real.log 2)) ^ (Nat.floor ((2 : ℝ) ^ (1 / η)) + 1)

/-- The divisor bound `τ(n) ≤ C_η n^η`. -/
theorem card_divisors_le {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤ constant η * (n : ℝ) ^ η := by
  classical
  set M := max 1 (1 / (η * Real.log 2))
  have hM : 1 ≤ M := le_max_left _ _
  set c : ℕ → ℝ := fun p => if (p : ℝ) < 2 ^ (1 / η) then M else 1
  have hfac : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) ≤ c p * (p : ℝ) ^ ((n.factorization p : ℝ) * η) :=
    fun p hp => prime_factor_le hη (Nat.prime_of_mem_primeFactors hp) _
  have hprod : (n.divisors.card : ℝ) ≤
      (∏ p ∈ n.primeFactors, c p) * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * η) := by
    rw [Nat.card_divisors hn, ← Finset.prod_mul_distrib]
    push_cast
    exact Finset.prod_le_prod (fun p _ => by positivity) hfac
  have hn' : ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * η) = (n : ℝ) ^ η := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod,
      ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hc : ∏ p ∈ n.primeFactors, c p ≤ constant η := by
    have hsub : ∏ p ∈ n.primeFactors, c p =
        ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < 2 ^ (1 / η)), M := by
      rw [Finset.prod_filter]
    rw [hsub, Finset.prod_const]
    apply pow_le_pow_right₀ hM
    calc (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < 2 ^ (1 / η))).card
        ≤ (Finset.range (Nat.floor ((2 : ℝ) ^ (1 / η)) + 1)).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact Nat.le_floor hp.2.le
      _ = _ := Finset.card_range _
  calc (n.divisors.card : ℝ) ≤ _ := hprod
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ η := by rw [hn']
    _ ≤ constant η * (n : ℝ) ^ η := mul_le_mul_of_nonneg_right hc (by positivity)

end Cubic.Counting.DivisorBound
