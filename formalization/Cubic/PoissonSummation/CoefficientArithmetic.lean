import Cubic.PoissonSummation.LocalCoefficients
import Cubic.PoissonSummation.ResidueParts

/-!
# Arithmetic functions for the coefficient formula

This supplies the finite arithmetic behind `thm:heightZetaFunctionFormula`.
`divisorWeight` is the product of the split and inert prime-power weights;
`coefficientDivisorSum` sums it over actual positive divisors.

The prime 3 has weight one in this auxiliary divisor sum, as it does in the
paper's expression `3^ω(P₁(d)) (-1)^Ω(P₂(d))`. Thus the sum agrees with the
proposed height coefficients only away from 3. Identifying it with geometric
height counts or a convergent Dirichlet series is a separate target.
-/

namespace Cubic.PoissonSummation

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- The residue-class weight of a prime power; the exponent-zero value is one. -/
def primePowerWeight (p k : ℕ) : ℤ :=
  if k = 0 then 1 else if p % 3 = 1 then 3 else if p % 3 = 2 then (-1) ^ k else 1

@[simp]
theorem primePowerWeight_zero (p : ℕ) : primePowerWeight p 0 = 1 := by
  simp [primePowerWeight]

/-- The arithmetic weight in the divisor formula, expressed by prime factorization. -/
def divisorWeight : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else n.factorization.prod primePowerWeight
  map_zero' := by simp

theorem divisorWeight_apply {n : ℕ} (hn : n ≠ 0) :
    divisorWeight n = n.factorization.prod primePowerWeight := by
  simp [divisorWeight, hn]

@[simp]
theorem divisorWeight_one : divisorWeight 1 = 1 := by
  simp [divisorWeight]

/-- The weight is multiplicative on coprime inputs, including the zero cases. -/
theorem divisorWeight_multiplicative : divisorWeight.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨divisorWeight_one, ?_⟩
  intro m n hm hn hcop
  rw [divisorWeight_apply (mul_ne_zero hm hn), divisorWeight_apply hm,
    divisorWeight_apply hn, Nat.factorization_mul hm hn]
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors

/-- Evaluate the global weight at a prime power, including `p^0 = 1`. -/
theorem divisorWeight_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorWeight (p ^ k) = primePowerWeight p k := by
  rw [divisorWeight_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index (primePowerWeight_zero p)

/-- Exact agreement with the paper's weight `3^ω(P₁(n)) (-1)^Ω(P₂(n))`. -/
theorem divisorWeight_eq_residueParts {n : ℕ} (hn : n ≠ 0) :
    divisorWeight n =
      (3 : ℤ) ^ cardDistinctFactors (primeResiduePart 1 n) *
      (-1 : ℤ) ^ cardFactors (primeResiduePart 2 n) := by
  rw [divisorWeight_apply hn, pow_cardDistinctFactors_primeResiduePart,
    pow_cardFactors_primeResiduePart, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  by_cases hsplit : p % 3 = 1
  · simp [primePowerWeight, hk, hsplit]
  · by_cases hinert : p % 3 = 2 <;> simp [primePowerWeight, hk, hsplit, hinert]

/-- The auxiliary divisor sum is Dirichlet convolution with the constant-one function. -/
def coefficientDivisorSum : ArithmeticFunction ℤ := divisorWeight * ζ

/-- Convolution is precisely the sum over positive divisors. -/
theorem coefficientDivisorSum_apply (n : ℕ) :
    coefficientDivisorSum n = ∑ d ∈ n.divisors, divisorWeight d := by
  exact coe_mul_zeta_apply

/-- The literal divisor formula from `thm:heightZetaFunctionFormula`.
This identifies an arithmetic expression; its interpretation as a height count is open. -/
theorem coefficientDivisorSum_eq_paper_formula (n : ℕ) :
    coefficientDivisorSum n = ∑ d ∈ n.divisors,
      (3 : ℤ) ^ cardDistinctFactors (primeResiduePart 1 d) *
      (-1 : ℤ) ^ cardFactors (primeResiduePart 2 d) := by
  rw [coefficientDivisorSum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  exact divisorWeight_eq_residueParts (Nat.pos_of_mem_divisors hd).ne'

/-- The global divisor sum is multiplicative. -/
theorem coefficientDivisorSum_multiplicative : coefficientDivisorSum.IsMultiplicative := by
  exact divisorWeight_multiplicative.mul isMultiplicative_zeta.natCast

/-- Reducing an actual prime-power divisor sum to exponent weights. -/
theorem coefficientDivisorSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coefficientDivisorSum (p ^ k) = ∑ j ∈ range (k + 1), primePowerWeight p j := by
  rw [coefficientDivisorSum_apply, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j _
  exact divisorWeight_prime_pow hp j

theorem primePowerWeight_split {p : ℕ} (hp : p % 3 = 1) (k : ℕ) :
    primePowerWeight p k = (splitDivisorWeight k : ℤ) := by
  by_cases hk : k = 0 <;> simp [primePowerWeight, splitDivisorWeight, hp, hk]

theorem primePowerWeight_inert {p : ℕ} (hp : p % 3 = 2) (k : ℕ) :
    primePowerWeight p k = (-1 : ℤ) ^ k := by
  by_cases hk : k = 0 <;> simp [primePowerWeight, hp, hk]

/-- The split local coefficient is `3k + 1`. -/
theorem coefficientDivisorSum_split {p : ℕ} (hp : p.Prime) (hres : p % 3 = 1) (k : ℕ) :
    coefficientDivisorSum (p ^ k) = 3 * (k : ℤ) + 1 := by
  rw [coefficientDivisorSum_prime_pow hp]
  simp_rw [primePowerWeight_split hres]
  exact_mod_cast sum_splitDivisorWeight k

/-- The inert local coefficient is one at even exponents. -/
theorem coefficientDivisorSum_inert_even {p : ℕ} (hp : p.Prime)
    (hres : p % 3 = 2) (k : ℕ) : coefficientDivisorSum (p ^ (2 * k)) = 1 := by
  rw [coefficientDivisorSum_prime_pow hp]
  simp_rw [primePowerWeight_inert hres]
  exact sum_inert_weights_even_exponent k

/-- The inert local coefficient is zero at odd exponents. -/
theorem coefficientDivisorSum_inert_odd {p : ℕ} (hp : p.Prime)
    (hres : p % 3 = 2) (k : ℕ) : coefficientDivisorSum (p ^ (2 * k + 1)) = 0 := by
  rw [coefficientDivisorSum_prime_pow hp]
  simp_rw [primePowerWeight_inert hres]
  exact sum_inert_weights_odd_exponent k

/-- At 3 the auxiliary divisor sum is `k + 1`, not the height-series coefficient.
The paper only asserts the divisor formula for integers not divisible by 3. -/
theorem coefficientDivisorSum_three_pow (k : ℕ) :
    coefficientDivisorSum (3 ^ k) = (k : ℤ) + 1 := by
  rw [coefficientDivisorSum_prime_pow (by decide : Nat.Prime 3)]
  simp [primePowerWeight]

/-- The literal split divisor sum in the manuscript, using mathlib's `ω`. -/
theorem sum_three_pow_cardDistinctFactors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, (3 : ℕ) ^ cardDistinctFactors d = 3 * k + 1 := by
  rw [Nat.sum_divisors_prime_pow hp]
  convert sum_splitDivisorWeight k using 1
  apply sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · simp [hj, splitDivisorWeight]
  · simp [cardDistinctFactors_apply_prime_pow hp hj, splitDivisorWeight, hj]

/-- The literal inert divisor sum in the manuscript, using mathlib's `Ω`. -/
theorem sum_neg_one_pow_cardFactors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, (-1 : ℤ) ^ cardFactors d =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp [cardFactors_apply_prime_pow hp]

/-- The precise finite factorization underlying reduction to prime powers. -/
theorem coefficientDivisorSum_factorization {n : ℕ} (hn : n ≠ 0) :
    coefficientDivisorSum n =
      n.factorization.prod (fun p k => ∑ d ∈ (p ^ k).divisors, divisorWeight d) := by
  rw [coefficientDivisorSum_multiplicative.multiplicative_factorization
    coefficientDivisorSum hn]
  simp_rw [coefficientDivisorSum_apply]

end Cubic.PoissonSummation
