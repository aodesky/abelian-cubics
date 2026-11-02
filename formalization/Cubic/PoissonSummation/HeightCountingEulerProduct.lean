import Cubic.PoissonSummation.HeightCountingCoefficients
import Cubic.PoissonSummation.HeightZetaEulerExtraction
import Cubic.PoissonSummation.LatticeSeries
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The convergent Dirichlet series of the proposed counting coefficients

Follow the paper's prime-power comparison: the split coefficients `3k+1`
give `(1+2x)/(1-x)^2`, inert parity gives `1/(1-x^2)`, and the factor at
three is one. Mathlib's Euler-product theorem then identifies the arithmetic
Dirichlet series with the already constructed height Euler expression.
Convergence on `Re(z)>3` suffices for the ensuing uniqueness argument.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightCountingEulerProduct

open HeightCountingCoefficients FiniteEulerProduct

def term (z : ℂ) (n : ℕ) : ℂ := LSeries.term (fun n => (coefficient n : ℂ)) z n

theorem term_eq (z : ℂ) (n : ℕ) :
    term z n = (coefficient n : ℂ) * (n : ℂ) ^ (-z) :=
  LSeries.term_def₀ (by simp) z n

theorem term_one (z : ℂ) : term z 1 = 1 := by
  simp [term_eq, multiplicative.1]

theorem term_mul (z : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    term z (m * n) = term z m * term z n := by
  simp only [term_eq, multiplicative.2 hmn, Int.cast_mul, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

theorem nat_pow_cpow (p k : ℕ) (z : ℂ) :
    ((p ^ k : ℕ) : ℂ) ^ (-z) = ((p : ℂ) ^ (-z)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ p k, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem term_prime_pow (p k : ℕ) (z : ℂ) :
    term z (p ^ k) = (coefficient (p ^ k) : ℂ) * ((p : ℂ) ^ (-z)) ^ k := by
  rw [term_eq, nat_pow_cpow]

theorem split_sum (p : SplitPrimes) (z : ℂ) (hz : 1 < z.re) :
    HasSum (fun k : ℕ => term z ((p.1 : ℕ) ^ k)) (splitFactor p z) := by
  have h := LatticeSeries.hasSum_split_geometric ((p.1 : ℂ) ^ (-z))
    ((Complex.norm_prime_cpow_le_one_half p.1 hz).trans_lt (by norm_num))
  simpa only [term_prime_pow, HeightCountingCoefficients.split p.1.2 p.2,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, splitFactor] using h

theorem inert_sum (p : InertPrimes) (z : ℂ) (hz : 1 < z.re) :
    HasSum (fun k : ℕ => term z ((p.1 : ℕ) ^ k)) (inertFactor p z) := by
  have hx : ‖((p.1 : ℂ) ^ (-z)) ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := Complex.norm_prime_cpow_le_one_half p.1 hz
    have := norm_nonneg ((p.1 : ℂ) ^ (-z))
    nlinarith
  have he : HasSum (fun k : ℕ => term z ((p.1 : ℕ) ^ (2 * k)))
      (1 - ((p.1 : ℂ) ^ (-z)) ^ 2)⁻¹ := by
    convert hasSum_geometric_of_norm_lt_one hx using 1
    funext k
    rw [term_prime_pow, HeightCountingCoefficients.inert_even p.1.2 p.2]
    simp only [Int.cast_one, one_mul, pow_mul]
  have ho : HasSum (fun k : ℕ => term z ((p.1 : ℕ) ^ (2 * k + 1))) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext k
    rw [term_prime_pow, HeightCountingCoefficients.inert_odd p.1.2 p.2]
    simp
  have hpow : (p.1 : ℂ) ^ (-(2 * z)) = ((p.1 : ℂ) ^ (-z)) ^ 2 := by
    rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]
    norm_num
  simpa only [add_zero, inertFactor, hpow] using
    he.even_add_odd (f := fun k : ℕ => term z ((p.1 : ℕ) ^ k)) ho

theorem three_sum (z : ℂ) : HasSum (fun k : ℕ => term z (3 ^ k)) 1 := by
  have h : HasSum (fun k : ℕ => term z (3 ^ (k + 1))) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext k
    rw [term_eq, three_pow_succ]
    simp
  simpa only [pow_zero, term_one, add_zero] using
    h.zero_add (f := fun k : ℕ => term z (3 ^ k))

theorem euler_product_of_summable (z : ℂ) (h1 : 1 < z.re)
    (hsum : LSeriesSummable (fun n => (coefficient n : ℂ)) z) :
    LSeries (fun n => (coefficient n : ℂ)) z = HeightZetaFormulaData.eulerExpression z := by
  have hA : HasProd (fun p : Nat.Primes => ∑' k : ℕ, term z ((p : ℕ) ^ k))
      (LSeries (fun n => (coefficient n : ℂ)) z) :=
    EulerProduct.eulerProduct_hasProd (term_one z) (term_mul z)
      hsum.norm (by simp [term])
  have hi : HasProd (fun p : InertPrimes => ∑' k : ℕ, term z ((p.1 : ℕ) ^ k))
      (∏' p : InertPrimes, inertFactor p z) := by
    simpa only [(inert_sum _ z h1).tsum_eq] using (convergent_inert z h1).hasProd
  have hs : HasProd (fun p : SplitPrimes => ∑' k : ℕ, term z ((p.1 : ℕ) ^ k))
      (∏' p : SplitPrimes, splitFactor p z) := by
    simpa only [(split_sum _ z h1).tsum_eq] using (convergent_split z h1).hasProd
  have hP := hasProd_primes_mod_three
    (f := fun p : Nat.Primes => ∑' k : ℕ, term z ((p : ℕ) ^ k)) hi hs
  have h := hA.unique hP
  simpa only [primeThree, (three_sum z).tsum_eq, one_mul,
    HeightZetaEulerExtraction.eulerExpression_eq_unscaled_product z h1] using h

/-- The original convergence range used in the trace-one coefficient comparison. -/
theorem euler_product (z : ℂ) (hz : 3 < z.re) :
    LSeries (fun n => (coefficient n : ℂ)) z = HeightZetaFormulaData.eulerExpression z :=
  euler_product_of_summable z (by linarith) (series_summable z hz)

end Cubic.PoissonSummation.HeightCountingEulerProduct
