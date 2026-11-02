import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The rational product formula in logarithmic form

Use mathlib's finite prime factorization and logarithm identity. The conclusion
is a convergent sum of the actual p-adic norms, with the archimedean term and
sign explicit. This supplies the scalar product formula needed for the
original rational norm character, without a new external dependency.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalProductFormula

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem hasSum_factorization_log (n : ℕ) :
    HasSum (fun p : Nat.Primes => (n.factorization p : ℝ) * Real.log p) (Real.log n) := by
  have h : HasSum (fun p : ℕ => (n.factorization p : ℝ) * Real.log p) (Real.log n) := by
    rw [Real.log_nat_eq_sum_factorization n]
    apply hasSum_sum_of_ne_finset_zero
    intro p hp
    have hz : n.factorization p = 0 := by
      by_contra hn
      exact hp (Finsupp.mem_support_iff.mpr hn)
    simp only [hz, Nat.cast_zero, zero_mul]
  apply (hasSum_subtype_iff_of_support_subset ?_).mpr h
  intro p hp
  have hn : n.factorization p ≠ 0 := by
    intro hn
    simp [Function.mem_support, hn] at hp
  exact Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hn)

theorem log_norm_rat (p : Nat.Primes) (q : ℚ) (hq : q ≠ 0) :
    Real.log ‖(q : ℚ_[p])‖ = -(padicValRat p q : ℝ) * Real.log p := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
  push_cast
  rw [Real.log_zpow]
  simp

theorem hasSum_valuation_log (q : ℚ) :
    HasSum (fun p : Nat.Primes => (padicValRat p q : ℝ) * Real.log p)
      (Real.log q.num.natAbs - Real.log q.den) := by
  convert (hasSum_factorization_log q.num.natAbs).sub (hasSum_factorization_log q.den)
    using 1
  funext p
  rw [Nat.factorization_def _ p.2, Nat.factorization_def _ p.2]
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast]
  ring

theorem log_norm_eq_num_sub_den (q : ℚ) (hq : q ≠ 0) :
    Real.log ‖(q : ℝ)‖ = Real.log q.num.natAbs - Real.log q.den := by
  have hn : (q.num : ℝ) ≠ 0 := by exact_mod_cast (Rat.num_ne_zero.mpr hq)
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  conv_lhs => rw [← Rat.num_div_den q]
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr hd)]
  simp

/-- The finite logarithmic sum equals minus the archimedean logarithm. -/
theorem hasSum_log_norm (q : ℚ) (hq : q ≠ 0) :
    HasSum (fun p : Nat.Primes => Real.log ‖(q : ℚ_[p])‖) (-Real.log ‖(q : ℝ)‖) := by
  rw [log_norm_eq_num_sub_den q hq]
  convert (hasSum_valuation_log q).neg using 1
  funext p
  rw [log_norm_rat p q hq]
  ring

theorem log_product_formula (q : ℚ) (hq : q ≠ 0) :
    Real.log ‖(q : ℝ)‖ + ∑' p : Nat.Primes, Real.log ‖(q : ℚ_[p])‖ = 0 := by
  rw [(hasSum_log_norm q hq).tsum_eq]
  ring

end Cubic.PoissonSummation.RationalProductFormula
