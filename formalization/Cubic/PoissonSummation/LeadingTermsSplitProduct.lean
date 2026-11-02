import Cubic.PoissonSummation.LeadingTermsPrimeSums

/-!
# The simplified split correction product

This is the product of `1 - 2 / (p^(s/2) (p^(s/2)+1))` in the proof of
`prop:leadingTerms`. Prove the local identity and absolute, locally uniform
convergence on `Re(s)>1` before manipulating or differentiating its product.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsSplitProduct

open FiniteEulerProduct LeadingTermsLocalDerivatives

theorem inversePower_sq (p : Nat.Primes) (s : ℂ) :
    (p : ℂ) ^ (-s) = ((p : ℂ) ^ (-(s / 2))) ^ 2 := by
  simpa only [show (2 : ℂ) * (s / 2) = s by ring] using
    HeightZetaCorrectionProduct.primePower_two p (s / 2)

theorem inversePower_bound (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-(s / 2))‖ ≤ 3 / 4 := by
  have h := Complex.norm_prime_cpow_le_one_half p hs
  rw [inversePower_sq p s, norm_pow] at h
  nlinarith [norm_nonneg ((p : ℂ) ^ (-(s / 2)))]

theorem inversePower_add_bound (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    1 / 4 ≤ ‖1 + (p : ℂ) ^ (-(s / 2))‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-((p : ℂ) ^ (-(s / 2))))
  simp only [norm_one, norm_neg, sub_neg_eq_add] at h
  linarith [inversePower_bound p hs]

theorem inversePower_add_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    1 + (p : ℂ) ^ (-(s / 2)) ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (inversePower_add_bound p hs))

theorem inversePower_sub_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-(s / 2)) ≠ 0 := by
  intro he
  have hx := sub_eq_zero.mp he
  have hb := inversePower_bound p hs
  rw [← hx, norm_one] at hb
  norm_num at hb

theorem power_add_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (p : ℂ) ^ (s / 2) + 1 ≠ 0 := by
  intro he
  have hx := eq_neg_of_add_eq_zero_left he
  have hb := inversePower_bound p hs
  rw [Complex.cpow_neg, hx] at hb
  norm_num at hb

theorem splitFactor_inverse (p : SplitPrimes) {s : ℂ} (hs : 1 < s.re) :
    LeadingTermsData.splitFactor p s =
      1 - 2 * ((p.1 : ℂ) ^ (-(s / 2))) ^ 2 / (1 + (p.1 : ℂ) ^ (-(s / 2))) := by
  have hminus := inversePower_sub_ne_zero p.1 hs
  have hplus := inversePower_add_ne_zero p.1 hs
  rw [LeadingTermsData.splitFactor, ← splitCorrection_reciprocal _
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (prime_ne_zero p.1)))
    (by simpa only [Complex.cpow_neg] using hminus)
    (by simpa only [Complex.cpow_neg] using hplus) (power_add_ne_zero p.1 hs),
    ← Complex.cpow_neg, splitCorrection_quotient _ hminus hplus]

theorem splitFactor_deviation (p : SplitPrimes) {s : ℂ} (hs : 1 < s.re) :
    ‖LeadingTermsData.splitFactor p s - 1‖ ≤ 8 * ‖(p.1 : ℂ) ^ (-s)‖ := by
  rw [splitFactor_inverse p hs]
  have he : 1 - 2 * ((p.1 : ℂ) ^ (-(s / 2))) ^ 2 /
      (1 + (p.1 : ℂ) ^ (-(s / 2))) - 1 =
      -(2 * ((p.1 : ℂ) ^ (-(s / 2))) ^ 2 /
        (1 + (p.1 : ℂ) ^ (-(s / 2)))) := by ring
  rw [he, norm_neg, norm_div, norm_mul, norm_pow, inversePower_sq p.1 s, norm_pow]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) (inversePower_add_bound p.1 hs))).mpr
  nlinarith [mul_le_mul_of_nonneg_left (inversePower_add_bound p.1 hs)
    (sq_nonneg ‖(p.1 : ℂ) ^ (-(s / 2))‖)]

theorem absolute (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : SplitPrimes => ‖LeadingTermsData.splitFactor p s - 1‖) :=
  (((summable_prime_power hs).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 8).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => splitFactor_deviation p hs)

theorem multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : SplitPrimes => LeadingTermsData.splitFactor p s) := by
  simpa using multipliable_one_add_of_summable (absolute s hs)

theorem differentiable (p : SplitPrimes) :
    DifferentiableOn ℂ (LeadingTermsData.splitFactor p) {s : ℂ | 1 < s.re} := by
  have hpow : Differentiable ℂ (fun s : ℂ => (p.1 : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (.inl (prime_ne_zero p.1))
  exact (differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (2 : ℂ)).div
    (hpow.differentiableOn.mul (hpow.differentiableOn.add_const 1))
    (fun s hs => mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (prime_ne_zero p.1)))
      (power_add_ne_zero p.1 hs)))

theorem locally_uniform : HasProdLocallyUniformlyOn LeadingTermsData.splitFactor
    (fun s => ∏' p : SplitPrimes, LeadingTermsData.splitFactor p s) {s : ℂ | 1 < s.re} := by
  apply locally_uniform_of_majorants 1 LeadingTermsData.splitFactor
    (fun τ p => 8 * ‖(p.1 : ℂ) ^ (-(τ : ℂ))‖)
  · intro τ hτ
    exact ((summable_prime_power (z := (τ : ℂ)) hτ).subtype
      (fun p => (p : ℕ) % 3 = 1)).mul_left 8
  · intro τ hτ p s hs
    exact (splitFactor_deviation p (hτ.trans_le hs)).trans
      (mul_le_mul_of_nonneg_left (prime_power_le (p := p.1) hs) (by norm_num))
  · intro p
    exact (differentiable p).continuousOn

/-- Recombine the simplified split factor with the ordinary prime zeta factor. -/
theorem local_identity (p : SplitPrimes) {s : ℂ} (hs : 1 < s.re) :
    HeightZetaCorrectionProduct.split p (s / 2) =
      (1 - (p.1 : ℂ) ^ (-s)) * LeadingTermsData.splitFactor p s := by
  rw [HeightZetaCorrectionProduct.split_eq_polynomial, inversePower_sq p.1 s, splitFactor_inverse p hs,
    ← splitCorrection_quotient _ (inversePower_sub_ne_zero p.1 hs)
      (inversePower_add_ne_zero p.1 hs)]
  have hn : 1 - ((p.1 : ℂ) ^ (-(s / 2))) ^ 2 ≠ 0 := by
    rw [← inversePower_sq p.1 s]
    exact Complex.one_sub_prime_cpow_ne_zero p.1.2 hs
  field_simp

theorem absolute_at_two : Summable (fun p : SplitPrimes =>
    ‖(1 - 2 / ((p.1 : ℂ) * ((p.1 : ℂ) + 1))) - 1‖) := by
  simpa [LeadingTermsData.splitFactor] using absolute 2 (by norm_num)

end Cubic.PoissonSummation.LeadingTermsSplitProduct
