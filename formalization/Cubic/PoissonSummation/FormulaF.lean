import CubicTargets.PoissonSummation.FormulaF
import Cubic.PoissonSummation.HeightZetaCorrectionProduct

/-!
# Proof of `formula_f(z)`

The paper's proof is the local identity `(1 + 3x(1−x)^{-1})(1−x)^3 = 1 − 3x^2 + 2x^3`
at `x = p^{-z}` (`split_euler_cancellation`). The only additions are the convergence
of the three products for `Re z > 1`, used to multiply the infinite products factor
by factor: each deviation from `1` is `O(|p^{-z}|)` (or `O(|p^{-2z}|)` for the third
product, `HeightZetaCorrectionProduct.convergent_split`), and `∑_p |p^{-z}|` converges.
-/

noncomputable section

namespace Cubic.PoissonSummation.FormulaF

open CubicTargets.PoissonSummation.FormulaF

private theorem one_div_cpow (p : Nat.Primes) (w : ℂ) :
    1 / (p : ℂ) ^ w = (p : ℂ) ^ (-w) := by
  rw [Complex.cpow_neg, one_div]

private theorem norm_le_half (p : Nat.Primes) {z : ℂ} (hz : 1 < z.re) :
    ‖(p : ℂ) ^ (-z)‖ ≤ 1 / 2 := Complex.norm_prime_cpow_le_one_half p hz

theorem first_eq (z : ℂ) (p : SplitPrimes) :
    first z p = 1 + 3 * (p.1 : ℂ) ^ (-z) / (1 - (p.1 : ℂ) ^ (-z)) := by
  rw [first, one_div_cpow, div_eq_mul_inv 3, Complex.cpow_neg]
  ring

theorem second_eq (z : ℂ) (p : SplitPrimes) :
    second z p = (1 - (p.1 : ℂ) ^ (-z)) ^ 3 := by
  rw [second, one_div_cpow]

theorem third_eq (z : ℂ) (p : SplitPrimes) :
    third z p = HeightZetaCorrectionProduct.split p z := by
  rw [third, HeightZetaCorrectionProduct.split, div_eq_mul_one_div 3, one_div_cpow,
    div_eq_mul_one_div 2, one_div_cpow]

theorem multipliable_first (z : ℂ) (hz : 1 < z.re) : Multipliable (first z) := by
  have hs : Summable (fun p : SplitPrimes => ‖first z p - 1‖) := by
    apply (((FiniteEulerProduct.summable_prime_power hz).subtype
      (fun p => (p : ℕ) % 3 = 1)).mul_left 6).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    set x := (p.1 : ℂ) ^ (-z)
    have hx : ‖x‖ ≤ 1 / 2 := norm_le_half p.1 hz
    have hd : 1 / 2 ≤ ‖1 - x‖ := by
      have := norm_sub_norm_le (1 : ℂ) x
      simp only [norm_one] at this
      linarith
    have hpos : 0 < ‖1 - x‖ := by linarith
    rw [first_eq, add_sub_cancel_left, norm_div, norm_mul, div_le_iff₀ hpos]
    simp only [Function.comp_apply, RCLike.norm_ofNat]
    change 3 * ‖x‖ ≤ 6 * ‖x‖ * ‖1 - x‖
    nlinarith [norm_nonneg x]
  simpa using multipliable_one_add_of_summable hs

theorem multipliable_second (z : ℂ) (hz : 1 < z.re) : Multipliable (second z) := by
  have hs : Summable (fun p : SplitPrimes => ‖second z p - 1‖) := by
    apply (((FiniteEulerProduct.summable_prime_power hz).subtype
      (fun p => (p : ℕ) % 3 = 1)).mul_left 7).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    set x := (p.1 : ℂ) ^ (-z)
    have hx : ‖x‖ ≤ 1 / 2 := norm_le_half p.1 hz
    have he : second z p - 1 = -(3 * x) + 3 * x ^ 2 - x ^ 3 := by
      rw [second_eq]; ring
    rw [he]
    simp only [Function.comp_apply]
    change _ ≤ 7 * ‖x‖
    calc ‖-(3 * x) + 3 * x ^ 2 - x ^ 3‖
        ≤ ‖-(3 * x)‖ + ‖3 * x ^ 2‖ + ‖x ^ 3‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ = 3 * ‖x‖ + 3 * ‖x‖ ^ 2 + ‖x‖ ^ 3 := by
        simp only [norm_neg, norm_mul, norm_pow, RCLike.norm_ofNat]
      _ ≤ 7 * ‖x‖ := by nlinarith [norm_nonneg x]
  simpa using multipliable_one_add_of_summable hs

theorem multipliable_third (z : ℂ) (hz : 1 < z.re) : Multipliable (third z) := by
  have h : third z = fun p => HeightZetaCorrectionProduct.split p z := funext (third_eq z)
  rw [h]
  exact HeightZetaCorrectionProduct.convergent_split z (by linarith)

/-- The local identity at `x = p^{-z}`. -/
theorem local_eq (z : ℂ) (hz : 1 < z.re) (p : SplitPrimes) :
    first z p * second z p = third z p := by
  rw [first_eq, second_eq, third_eq, HeightZetaCorrectionProduct.split_eq_polynomial]
  exact split_euler_cancellation _ (Complex.one_sub_prime_cpow_ne_zero p.1.2 hz)

theorem «formula_f(z)» : Claim where
  multipliable_first := multipliable_first
  multipliable_second := multipliable_second
  multipliable_third := multipliable_third
  eq z hz := by
    have h := ((multipliable_first z hz).hasProd.mul (multipliable_second z hz).hasProd).congr_fun
      (fun p => (local_eq z hz p).symm)
    exact (h.unique (multipliable_third z hz).hasProd)

end Cubic.PoissonSummation.FormulaF
