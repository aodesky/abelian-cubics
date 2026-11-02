import Cubic.PoissonSummation.FiniteEulerProductHolomorphy
import Cubic.PoissonSummation.EulerFactors

/-!
# Holomorphic correction products on `Re z>1/2`

These are the exact two products displayed in `lemma:simplifiedZ(s)`.
Their deviations begin at `p^(-2z)`. Prove absolute and locally uniform
convergence directly on the open half-plane needed for the theorem.
The comparison with the actual Dedekind zeta function is established separately.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaCorrectionProduct

open FiniteEulerProduct

def inert (q : InertPrimes) (z : ℂ) : ℂ := 1 - (q.1 : ℂ) ^ (-(2 * z))

def split (p : SplitPrimes) (z : ℂ) : ℂ :=
  1 - 3 * (p.1 : ℂ) ^ (-(2 * z)) + 2 * (p.1 : ℂ) ^ (-(3 * z))

def value (z : ℂ) : ℂ := (∏' q : InertPrimes, inert q z) * ∏' p : SplitPrimes, split p z

theorem primePower_mul (p : Nat.Primes) (z : ℂ) (n : ℕ) :
    (p : ℂ) ^ (-((n : ℂ) * z)) = ((p : ℂ) ^ (-z)) ^ n := by
  rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]

theorem primePower_two (p : Nat.Primes) (z : ℂ) :
    (p : ℂ) ^ (-(2 * z)) = ((p : ℂ) ^ (-z)) ^ 2 := by
  simpa only [Nat.cast_ofNat] using primePower_mul p z 2

theorem primePower_three (p : Nat.Primes) (z : ℂ) :
    (p : ℂ) ^ (-(3 * z)) = ((p : ℂ) ^ (-z)) ^ 3 := by
  simpa only [Nat.cast_ofNat] using primePower_mul p z 3

theorem split_eq_polynomial (p : SplitPrimes) (z : ℂ) :
    split p z = Cubic.PoissonSummation.splitCorrection ((p.1 : ℂ) ^ (-z)) := by
  unfold split Cubic.PoissonSummation.splitCorrection
  rw [primePower_two, primePower_three]

private theorem primePower_norm_le_one (p : Nat.Primes) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(p : ℂ) ^ (-z)‖ ≤ 1 := by
  simpa using prime_power_le (p := p) hz

theorem inert_deviation (q : InertPrimes) (z : ℂ) :
    ‖inert q z - 1‖ = ‖(q.1 : ℂ) ^ (-(2 * z))‖ := by
  simp [inert]

theorem split_deviation (p : SplitPrimes) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖split p z - 1‖ ≤ 5 * ‖(p.1 : ℂ) ^ (-(2 * z))‖ := by
  rw [split_eq_polynomial, primePower_two]
  let x := (p.1 : ℂ) ^ (-z)
  have hx : ‖x‖ ≤ 1 := primePower_norm_le_one p.1 hz
  have he : Cubic.PoissonSummation.splitCorrection x - 1 = -(3 * x ^ 2) + 2 * x ^ 3 := by
    unfold Cubic.PoissonSummation.splitCorrection
    ring
  rw [he, norm_pow]
  have hn : ‖-(3 * x ^ 2) + 2 * x ^ 3‖ ≤ 3 * ‖x‖ ^ 2 + 2 * ‖x‖ ^ 3 := by
    calc
      _ ≤ ‖-(3 * x ^ 2)‖ + ‖2 * x ^ 3‖ := norm_add_le _ _
      _ = _ := by simp only [norm_neg, norm_mul, norm_pow]; norm_num
  have hc : ‖x‖ ^ 3 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  linarith

private theorem two_re_gt_one {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) : 1 < (2 * z).re := by
  norm_num [Complex.mul_re]
  linarith

theorem absolute_inert (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Summable (fun q : InertPrimes => ‖inert q z - 1‖) := by
  simp only [inert_deviation]
  exact (summable_prime_power (two_re_gt_one hz)).subtype (fun p => (p : ℕ) % 3 = 2)

theorem absolute_split (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Summable (fun p : SplitPrimes => ‖split p z - 1‖) := by
  apply (((summable_prime_power (two_re_gt_one hz)).subtype
    (fun p => (p : ℕ) % 3 = 1)).mul_left 5).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  exact split_deviation p z (by linarith)

theorem convergent_inert (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Multipliable (fun q : InertPrimes => inert q z) := by
  simpa using multipliable_one_add_of_summable (absolute_inert z hz)

theorem convergent_split (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Multipliable (fun p : SplitPrimes => split p z) := by
  simpa using multipliable_one_add_of_summable (absolute_split z hz)

theorem differentiable_inert (q : InertPrimes) : Differentiable ℂ (inert q) := by
  have hq : (q.1 : ℂ) ≠ 0 := by exact_mod_cast q.1.2.ne_zero
  exact (differentiable_const _).sub
    (((differentiable_const _).mul differentiable_id).neg.const_cpow (.inl hq))

theorem differentiable_split (p : SplitPrimes) : Differentiable ℂ (split p) := by
  have hp : (p.1 : ℂ) ≠ 0 := by exact_mod_cast p.1.2.ne_zero
  have h (n : ℂ) : Differentiable ℂ (fun z : ℂ => (p.1 : ℂ) ^ (-(n * z))) :=
    ((differentiable_const _).mul differentiable_id).neg.const_cpow (.inl hp)
  exact ((differentiable_const _).sub ((differentiable_const _).mul (h 2))).add
    ((differentiable_const _).mul (h 3))

private theorem majorant_le (p : Nat.Primes) {z : ℂ} {τ : ℝ} (hz : τ ≤ z.re) :
    ‖(p : ℂ) ^ (-(2 * z))‖ ≤ ‖(p : ℂ) ^ (-(2 * (τ : ℂ)))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.2.pos
  norm_num [Complex.mul_re]
  linarith

theorem locally_uniform_inert : HasProdLocallyUniformlyOn inert
    (fun z => ∏' q : InertPrimes, inert q z) {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  apply locally_uniform_of_majorants (1 / 2) inert
    (fun τ q => ‖(q.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖)
  · intro τ hτ
    exact (summable_prime_power (two_re_gt_one hτ)).subtype (fun p => (p : ℕ) % 3 = 2)
  · intro τ _ q z hz
    rw [inert_deviation]
    exact majorant_le q.1 hz
  · intro q
    exact (differentiable_inert q).continuous.continuousOn

theorem locally_uniform_split : HasProdLocallyUniformlyOn split
    (fun z => ∏' p : SplitPrimes, split p z) {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  apply locally_uniform_of_majorants (1 / 2) split
    (fun τ p => 5 * ‖(p.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖)
  · intro τ hτ
    exact ((summable_prime_power (two_re_gt_one hτ)).subtype
      (fun p => (p : ℕ) % 3 = 1)).mul_left 5
  · intro τ hτ p z hz
    exact (split_deviation p z (by linarith)).trans
      (mul_le_mul_of_nonneg_left (majorant_le p.1 hz) (by norm_num))
  · intro p
    exact (differentiable_split p).continuous.continuousOn

theorem differentiableOn_value :
    DifferentiableOn ℂ value {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  have hi := locally_uniform_inert.differentiableOn
    (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
      fun q _ => (differentiable_inert q).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  have hs := locally_uniform_split.differentiableOn
    (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
      fun p _ => (differentiable_split p).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact hi.mul hs

end Cubic.PoissonSummation.HeightZetaCorrectionProduct
