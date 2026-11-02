import Cubic.Counting.HeightCoefficientData
import Cubic.Counting.DivisorBound
import Cubic.PoissonSummation.HeightCountingIdentification
import Cubic.PoissonSummation.HeightCountingCoefficients
import Cubic.PoissonSummation.LocalCoefficients
import Cubic.PoissonSummation.HeightZetaCorrectionProduct

/-!
# Arithmetic inputs of `eqn:dSummatoryForGeneralTrace`

* The coefficient formula gives `0 ≤ d_n ≤ τ(n)³ ≪_η n^η`: at a split prime, `3k+1 ≤ (k+1)³`.
* The Euler product for `E(2s)` is absolutely convergent and uniformly bounded on `Re s ≥ β`.

The coefficient formula `d_n = coefficient n` (the multiplicative function of
`HeightCountingCoefficients`) is `HeightCountingIdentification.counts_eq_coefficient`, which is
proved from the Poisson summation input `PoissonWithDualMeasure.BlackBox`. The upper bounds on
`d_n` therefore carry that hypothesis. The bound `coefficient n ≤ τ(n)³` itself is unconditional.
-/

noncomputable section

namespace Cubic.Counting.HeightCoefficientBounds

open Cubic.Counting.HeightCoefficientData
open Cubic.PoissonSummation
open ArithmeticFunction

theorem d_nonneg (n : ℕ) : 0 ≤ d n := by
  unfold d
  positivity

/-! ### The coefficient formula and the divisor bound -/

/-- Local bound `0 ≤ a(p^k) ≤ (k+1)³` for the multiplicative coefficient. -/
theorem coefficient_prime_pow_bounds {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ HeightCountingCoefficients.coefficient (p ^ k) ∧
      HeightCountingCoefficients.coefficient (p ^ k) ≤ ((k : ℤ) + 1) ^ 3 := by
  have hk3 : (1 : ℤ) ≤ ((k : ℤ) + 1) ^ 3 := one_le_pow₀ (by omega)
  by_cases h3 : p = 3
  · subst h3
    rcases k with _ | k
    · simp [HeightCountingCoefficients.multiplicative.map_one]
    · rw [HeightCountingCoefficients.three_pow_succ]
      exact ⟨le_rfl, by positivity⟩
  have hres : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
    omega
  rcases hres with hres | hres
  · rw [HeightCountingCoefficients.split hp hres]
    have hloc := split_coefficient_le_divisor_cube k
    refine ⟨by positivity, ?_⟩
    exact_mod_cast hloc
  · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [HeightCountingCoefficients.inert_even hp hres]
      exact ⟨zero_le_one, hk3⟩
    · rw [HeightCountingCoefficients.inert_odd hp hres]
      exact ⟨le_rfl, by positivity⟩

/-- `0 ≤ a(n) ≤ τ(n)³` for the multiplicative coefficient, by multiplicativity of both sides. -/
theorem coefficient_bounds (n : ℕ) :
    0 ≤ HeightCountingCoefficients.coefficient n ∧
      HeightCountingCoefficients.coefficient n ≤ (n.divisors.card : ℤ) ^ 3 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hτ : (n.divisors.card : ℤ) ^ 3 =
      n.factorization.prod fun p k => ((k : ℤ) + 1) ^ 3 := by
    rw [← sigma_zero_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
    simp only [Finsupp.prod, Nat.cast_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [sigma_zero_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
    push_cast
    ring
  rw [hτ, HeightCountingCoefficients.multiplicative.multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  refine ⟨Finset.prod_nonneg fun p hp => ?_, Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_⟩
  · exact (coefficient_prime_pow_bounds (Nat.prime_of_mem_primeFactors hp) _).1
  · exact (coefficient_prime_pow_bounds (Nat.prime_of_mem_primeFactors hp) _).1
  · exact (coefficient_prime_pow_bounds (Nat.prime_of_mem_primeFactors hp) _).2

/-- `d_n ≤ τ(n)³`, by multiplicativity and the local bound `3k+1 ≤ (k+1)³`.
The coefficient formula `d_n = a(n)` is proved from the Poisson summation input. -/
theorem d_le_divisor_cube
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) (n : ℕ) :
    d n ≤ (n.divisors.card : ℝ) ^ 3 := by
  have h := HeightCountingIdentification.counts_eq_coefficient hPoisson n
  have hb := (coefficient_bounds n).2
  rw [← h] at hb
  unfold d
  exact_mod_cast hb

theorem d_le_rpow
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (η : ℝ) (hη : 0 < η) : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → d n ≤ K * (n : ℝ) ^ η := by
  refine ⟨DivisorBound.constant (η / 3) ^ 3, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hτ := DivisorBound.card_divisors_le (η := η / 3) (by positivity) hn0
  calc
    d n ≤ (n.divisors.card : ℝ) ^ 3 := d_le_divisor_cube hPoisson n
    _ ≤ (DivisorBound.constant (η / 3) * (n : ℝ) ^ (η / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hτ 3
    _ = DivisorBound.constant (η / 3) ^ 3 * (n : ℝ) ^ η := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (η / 3)), ← Real.rpow_mul (by positivity)]
      norm_num

/-! ### The correction product `E(2s)` on `Re s ≥ β` -/

/-- A convergent product with summable deviations is bounded by the exponential of the sum
of the deviation bounds; this is the limit of the same bound for finite partial products. -/
theorem norm_tprod_le_exp {ι : Type*} {f : ι → ℂ} (hf : Multipliable f) {a : ι → ℝ}
    (ha : Summable a) (hfa : ∀ i, ‖f i - 1‖ ≤ a i) :
    ‖∏' i, f i‖ ≤ Real.exp (∑' i, a i) := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hfa i)
  refine le_of_tendsto' (hf.hasProd.norm) fun s => ?_
  have hfi : ∀ i, ‖f i‖ ≤ Real.exp (a i) := fun i => by
    calc
      ‖f i‖ = ‖(f i - 1) + 1‖ := by ring_nf
      _ ≤ ‖f i - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ a i + 1 := by simpa using hfa i
      _ ≤ Real.exp (a i) := Real.add_one_le_exp _
  calc
    ∏ i ∈ s, ‖f i‖ ≤ ∏ i ∈ s, Real.exp (a i) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hfi i
    _ = Real.exp (∑ i ∈ s, a i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' i, a i) :=
      Real.exp_le_exp.mpr (ha.sum_le_tsum s fun i _ => ha0 i)

private theorem prime_power_two_le (p : Nat.Primes) {z : ℂ} {β : ℝ} (hz : β ≤ z.re) :
    ‖(p : ℂ) ^ (-(2 * z))‖ ≤ ‖(p : ℂ) ^ (-((2 * β : ℝ) : ℂ))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.2.pos
  norm_num [Complex.mul_re]
  linarith

private theorem summable_prime_power_two {β : ℝ} (hβ : 1 / 2 < β) :
    Summable (fun p : Nat.Primes => ‖(p : ℂ) ^ (-((2 * β : ℝ) : ℂ))‖) :=
  FiniteEulerProduct.summable_prime_power (by simp; linarith)

/-- The correction product `value z` is uniformly bounded on `Re z ≥ β`, for `β > 1/2`. -/
theorem value_bounded (β : ℝ) (hβ : 1 / 2 < β) :
    ∃ C : ℝ, ∀ z : ℂ, β ≤ z.re → ‖HeightZetaCorrectionProduct.value z‖ ≤ C := by
  set m := fun p : Nat.Primes => ‖(p : ℂ) ^ (-((2 * β : ℝ) : ℂ))‖
  have hm := summable_prime_power_two hβ
  have hmi : Summable (fun q : FiniteEulerProduct.InertPrimes => m q.1) :=
    hm.subtype (fun p => (p : ℕ) % 3 = 2)
  have hms : Summable (fun p : FiniteEulerProduct.SplitPrimes => 5 * m p.1) :=
    (hm.subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 5
  refine ⟨Real.exp (∑' q : FiniteEulerProduct.InertPrimes, m q.1) *
    Real.exp (∑' p : FiniteEulerProduct.SplitPrimes, 5 * m p.1), fun z hz => ?_⟩
  have hz' : (1 / 2 : ℝ) < z.re := by linarith
  unfold HeightZetaCorrectionProduct.value
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.exp_pos _).le
  · refine norm_tprod_le_exp (HeightZetaCorrectionProduct.convergent_inert z hz') hmi
      fun q => ?_
    rw [HeightZetaCorrectionProduct.inert_deviation]
    exact prime_power_two_le q.1 hz
  · refine norm_tprod_le_exp (HeightZetaCorrectionProduct.convergent_split z hz') hms
      fun p => ?_
    exact (HeightZetaCorrectionProduct.split_deviation p z (by linarith)).trans
      (mul_le_mul_of_nonneg_left (prime_power_two_le p.1 hz) (by norm_num))

/-- `E(2s)` is uniformly bounded on `Re s ≥ β`, for `β > 1/2`. -/
theorem correction_bounded (β : ℝ) (hβ : 1 / 2 < β) :
    ∃ C : ℝ, ∀ s : ℂ, β ≤ s.re → ‖LeadingTermsData.correction (2 * s)‖ ≤ C := by
  obtain ⟨C, hC⟩ := value_bounded β hβ
  refine ⟨4 * C, fun s hs => ?_⟩
  have h2 : 2 * s / 2 = s := by ring
  unfold LeadingTermsData.correction
  rw [h2, norm_mul, norm_pow]
  have h3 : ‖(3 : ℂ) ^ (-s)‖ ≤ 1 := by
    have := Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (n := 3) (by norm_num)
      (w := -s) (z := 0) (by simp; linarith)
    simpa using this
  have h1 : ‖1 - (3 : ℂ) ^ (-s)‖ ≤ 2 := by
    calc
      ‖1 - (3 : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(3 : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ 2 := by simp only [norm_one]; linarith
  have hv := hC s hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hv
  calc
    ‖1 - (3 : ℂ) ^ (-s)‖ ^ 2 * ‖HeightZetaCorrectionProduct.value s‖
        ≤ 2 ^ 2 * C := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) hv
          (norm_nonneg _) (by positivity)
    _ = 4 * C := by norm_num

end Cubic.Counting.HeightCoefficientBounds
