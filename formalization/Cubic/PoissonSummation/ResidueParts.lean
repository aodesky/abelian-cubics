import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The residue-class parts of a positive integer

`primeResiduePart j n` implements `P_j(n)` in `thm:heightZetaFunctionFormula`
and `thm:exactFormula`: retain exactly the prime powers whose prime is `j` modulo 3.
The construction is defined at zero as one, but its divisor characterization requires
`n ≠ 0`, matching the positive inputs in the paper.
-/

namespace Cubic.PoissonSummation

open Finset ArithmeticFunction

/-- The factor of `n` supported on primes congruent to `j` modulo three. -/
def primeResiduePart (j n : ℕ) : ℕ :=
  (n.factorization.filter fun p => p % 3 = j).prod (· ^ ·)

/-- Filtering the prime factorization introduces no new prime factors. -/
theorem primeResiduePart_factorization (j n : ℕ) :
    (primeResiduePart j n).factorization = n.factorization.filter (fun p => p % 3 = j) := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem primeResiduePart_ne_zero (j n : ℕ) : primeResiduePart j n ≠ 0 := by
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

/-- `P_j(n)` really divides `n` for positive `n`. -/
theorem primeResiduePart_dvd (j : ℕ) {n : ℕ} (hn : n ≠ 0) : primeResiduePart j n ∣ n := by
  apply (Nat.factorization_le_iff_dvd (primeResiduePart_ne_zero j n) hn).mp
  rw [primeResiduePart_factorization]
  intro p
  simp only [Finsupp.filter_apply]
  split <;> omega

/-- The distinct prime factors of `P_j(n)` are exactly the selected prime factors. -/
theorem primeResiduePart_primeFactors (j n : ℕ) :
    (primeResiduePart j n).primeFactors = n.primeFactors.filter (fun p => p % 3 = j) := by
  rw [← Nat.support_factorization, primeResiduePart_factorization,
    Finsupp.support_filter, Nat.support_factorization]

/-- The defining characterization of the largest divisor supported in one residue class. -/
theorem dvd_primeResiduePart_iff (j : ℕ) {d n : ℕ} (hn : n ≠ 0) :
    d ∣ primeResiduePart j n ↔ d ∣ n ∧ ∀ p ∈ d.primeFactors, p % 3 = j := by
  constructor
  · intro hd
    refine ⟨hd.trans (primeResiduePart_dvd j hn), ?_⟩
    intro p hp
    have hpart := Nat.primeFactors_mono hd (primeResiduePart_ne_zero j n) hp
    rw [primeResiduePart_primeFactors] at hpart
    exact (Finset.mem_filter.mp hpart).2
  · rintro ⟨hd, hres⟩
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
    apply (Nat.factorization_le_iff_dvd hd0 (primeResiduePart_ne_zero j n)).mp
    rw [primeResiduePart_factorization]
    have hle := (Nat.factorization_le_iff_dvd hd0 hn).mpr hd
    intro p
    by_cases hp : p % 3 = j
    · simpa only [Finsupp.filter_apply, if_pos hp] using hle p
    · simp only [Finsupp.filter_apply, if_neg hp, Nat.le_zero]
      by_contra he
      exact hp (hres p (Finsupp.mem_support_iff.mpr he))

/-- Convert the paper's `ω(P_j(n))` into a count of selected primes. -/
theorem cardDistinctFactors_primeResiduePart (j n : ℕ) :
    cardDistinctFactors (primeResiduePart j n) =
      (n.primeFactors.filter fun p => p % 3 = j).card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    primeResiduePart_primeFactors]

/-- Powers of `ω(P_j(n))` expressed as a product over the original primes. -/
theorem pow_cardDistinctFactors_primeResiduePart (b : ℤ) (j n : ℕ) :
    b ^ cardDistinctFactors (primeResiduePart j n) =
      ∏ p ∈ n.primeFactors, if p % 3 = j then b else 1 := by
  rw [cardDistinctFactors_primeResiduePart, ← Finset.prod_const, Finset.prod_filter]

/-- Powers of `Ω(P_j(n))` expressed as a product with multiplicities. -/
theorem pow_cardFactors_primeResiduePart (b : ℤ) (j n : ℕ) :
    b ^ cardFactors (primeResiduePart j n) =
      ∏ p ∈ n.primeFactors, if p % 3 = j then b ^ n.factorization p else 1 := by
  rw [cardFactors_eq_sum_factorization, primeResiduePart_factorization,
    Finsupp.sum_filter_index, ← Finset.prod_pow_eq_pow_sum,
    Finsupp.support_filter, Nat.support_factorization, Finset.prod_filter]

end Cubic.PoissonSummation
