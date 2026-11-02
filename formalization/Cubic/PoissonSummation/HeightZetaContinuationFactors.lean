import Cubic.PoissonSummation.HeightZetaCorrectionProduct
import Cubic.PoissonSummation.QuadraticLEulerProduct

/-!
# The three products in the paper's continuation argument

The inert fourth-power product converges on `Re z > 1/4`. The exact
remaining split factor is `(1-3x²+2x³)/(1-x²)³`, whose deviations start
in degree three; its product converges on `Re z > 1/3`. The ordinary
split product at `2z` converges on `Re z > 1/2`. Their combination with
the actual entire `L(2z,χ)` is the correction product in the paper.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContinuationFactors

open FiniteEulerProduct HeightZetaFormulaData HeightZetaEulerExtraction
open scoped Topology

def remainingCorrection (x : ℂ) : ℂ :=
  (1 - 3 * x ^ 2 + 2 * x ^ 3) / (1 - x ^ 2) ^ 3

def inertFourth (q : InertPrimes) (z : ℂ) : ℂ :=
  1 - (q.1 : ℂ) ^ (-(4 * z))

def splitBase (p : SplitPrimes) (z : ℂ) : ℂ :=
  1 - (p.1 : ℂ) ^ (-(2 * z))

def remainingSplit (p : SplitPrimes) (z : ℂ) : ℂ :=
  remainingCorrection ((p.1 : ℂ) ^ (-z))

def inertProduct (z : ℂ) : ℂ := ∏' q : InertPrimes, inertFourth q z

def splitProduct (z : ℂ) : ℂ := ∏' p : SplitPrimes, splitBase p z

def remainingProduct (z : ℂ) : ℂ := ∏' p : SplitPrimes, remainingSplit p z

theorem remaining_deviation_identity (x : ℂ) (hx : 1 - x ^ 2 ≠ 0) :
    remainingCorrection x - 1 = (2 * x ^ 3 - 3 * x ^ 4 + x ^ 6) / (1 - x ^ 2) ^ 3 := by
  unfold remainingCorrection
  field_simp
  ring

theorem remaining_expansion_identity (x : ℂ) (hx : 1 - x ^ 2 ≠ 0) :
    remainingCorrection x - (1 + 2 * x ^ 3 - 3 * x ^ 4) =
      x ^ 5 * (6 - 8 * x - 6 * x ^ 2 + 9 * x ^ 3 + 2 * x ^ 4 - 3 * x ^ 5) /
        (1 - x ^ 2) ^ 3 := by
  unfold remainingCorrection
  field_simp
  ring

theorem inversePower_bound (p : Nat.Primes) {z : ℂ} (hz : (1 / 3 : ℝ) < z.re) :
    ‖(p : ℂ) ^ (-z)‖ ≤ 4 / 5 := by
  have h3 : 1 < (3 * z).re := by norm_num [Complex.mul_re]; linarith
  have h := Complex.norm_prime_cpow_le_one_half p h3
  rw [HeightZetaCorrectionProduct.primePower_three, norm_pow] at h
  by_contra hn
  have hp := pow_lt_pow_left₀ (lt_of_not_ge hn) (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (by decide : (3 : ℕ) ≠ 0)
  norm_num at hp
  linarith

theorem remaining_denominator_bound (x : ℂ) (hx : ‖x‖ ≤ 4 / 5) :
    1 / 4 ≤ ‖1 - x ^ 2‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (x ^ 2)
  simp only [norm_one, norm_pow] at h
  nlinarith [norm_nonneg x]

theorem remaining_denominator_ne_zero (x : ℂ) (hx : ‖x‖ ≤ 4 / 5) :
    1 - x ^ 2 ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (remaining_denominator_bound x hx))

theorem remaining_expansion :
    (fun x : ℂ => remainingCorrection x - 1 - 2 * x ^ 3 + 3 * x ^ 4)
      =O[𝓝 (0 : ℂ)] (fun x : ℂ => x ^ 5) := by
  let g : ℂ → ℂ := fun x =>
    (6 - 8 * x - 6 * x ^ 2 + 9 * x ^ 3 + 2 * x ^ 4 - 3 * x ^ 5) / (1 - x ^ 2) ^ 3
  have hc : ContinuousAt g 0 :=
    (show ContinuousAt
      (fun x : ℂ => 6 - 8 * x - 6 * x ^ 2 + 9 * x ^ 3 + 2 * x ^ 4 - 3 * x ^ 5) 0
      by fun_prop).div
        (show ContinuousAt (fun x : ℂ => (1 - x ^ 2) ^ 3) 0 by fun_prop)
        (by norm_num)
  have hb := (Asymptotics.isBigO_refl (fun x : ℂ => x ^ 5) (𝓝 (0 : ℂ))).mul
    (hc.tendsto.isBigO_one ℂ)
  have hU : {x : ℂ | ‖x‖ < 4 / 5} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  have he : (fun x : ℂ => remainingCorrection x - 1 - 2 * x ^ 3 + 3 * x ^ 4)
      =ᶠ[𝓝 (0 : ℂ)] (fun x => x ^ 5 * g x) := by
    filter_upwards [hU] with x hx
    calc
      remainingCorrection x - 1 - 2 * x ^ 3 + 3 * x ^ 4 =
          remainingCorrection x - (1 + 2 * x ^ 3 - 3 * x ^ 4) := by ring
      _ = x ^ 5 * g x := by
        simpa only [g, mul_div_assoc] using
          remaining_expansion_identity x (remaining_denominator_ne_zero x hx.le)
  simpa only [mul_one] using hb.congr' he.symm Filter.EventuallyEq.rfl

theorem remaining_deviation_bound (x : ℂ) (hx : ‖x‖ ≤ 4 / 5) :
    ‖remainingCorrection x - 1‖ ≤ 384 * ‖x‖ ^ 3 := by
  have hden := remaining_denominator_bound x hx
  have hn := remaining_denominator_ne_zero x hx
  have hx1 : ‖x‖ ≤ 1 := by linarith
  have h4 : ‖x‖ ^ 4 ≤ ‖x‖ ^ 3 :=
    pow_le_pow_of_le_one (norm_nonneg x) hx1 (by decide)
  have h6 : ‖x‖ ^ 6 ≤ ‖x‖ ^ 3 :=
    pow_le_pow_of_le_one (norm_nonneg x) hx1 (by decide)
  have hnum : ‖2 * x ^ 3 - 3 * x ^ 4 + x ^ 6‖ ≤ 6 * ‖x‖ ^ 3 := by
    have h := (norm_add_le (2 * x ^ 3 - 3 * x ^ 4) (x ^ 6)).trans
      (add_le_add (norm_sub_le (2 * x ^ 3) (3 * x ^ 4)) (le_refl ‖x ^ 6‖))
    simp only [norm_mul, norm_pow] at h
    norm_num only [Complex.norm_ofNat] at h
    linarith
  rw [remaining_deviation_identity x hn, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < ‖1 - x ^ 2‖) 3)).mpr
  have hc : (1 / 64 : ℝ) ≤ ‖1 - x ^ 2‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hden 3
    norm_num at h
    exact h
  have hm := mul_le_mul_of_nonneg_left hc
    (by positivity : 0 ≤ 384 * ‖x‖ ^ 3)
  nlinarith

theorem absolute_inert (z : ℂ) (hz : (1 / 4 : ℝ) < z.re) :
    Summable (fun q : InertPrimes => ‖inertFourth q z - 1‖) := by
  simp only [inertFourth, sub_sub_cancel_left, norm_neg]
  exact (summable_prime_power (z := 4 * z) (by norm_num [Complex.mul_re]; linarith)).subtype
    (fun p => (p : ℕ) % 3 = 2)

theorem absolute_splitBase (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Summable (fun p : SplitPrimes => ‖splitBase p z - 1‖) := by
  simp only [splitBase, sub_sub_cancel_left, norm_neg]
  exact (summable_prime_power (z := 2 * z) (by norm_num [Complex.mul_re]; linarith)).subtype
    (fun p => (p : ℕ) % 3 = 1)

theorem absolute_remaining (z : ℂ) (hz : (1 / 3 : ℝ) < z.re) :
    Summable (fun p : SplitPrimes => ‖remainingSplit p z - 1‖) := by
  have h3 : 1 < (3 * z).re := by norm_num [Complex.mul_re]; linarith
  apply (((summable_prime_power h3).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left
    384).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  change ‖remainingSplit p z - 1‖ ≤ 384 * ‖(p.1 : ℂ) ^ (-(3 * z))‖
  rw [HeightZetaCorrectionProduct.primePower_three, norm_pow]
  exact remaining_deviation_bound _ (inversePower_bound p.1 hz)

theorem multipliable_inert (z : ℂ) (hz : (1 / 4 : ℝ) < z.re) :
    Multipliable (fun q : InertPrimes => inertFourth q z) := by
  simpa using multipliable_one_add_of_summable (absolute_inert z hz)

theorem multipliable_splitBase (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    Multipliable (fun p : SplitPrimes => splitBase p z) := by
  simpa using multipliable_one_add_of_summable (absolute_splitBase z hz)

theorem multipliable_remaining (z : ℂ) (hz : (1 / 3 : ℝ) < z.re) :
    Multipliable (fun p : SplitPrimes => remainingSplit p z) := by
  simpa using multipliable_one_add_of_summable (absolute_remaining z hz)

theorem differentiable_inert (q : InertPrimes) : Differentiable ℂ (inertFourth q) := by
  exact (differentiable_const _).sub
    (((differentiable_const _).mul differentiable_id).neg.const_cpow
      (.inl (by exact_mod_cast q.1.2.ne_zero)))

theorem differentiable_splitBase (p : SplitPrimes) : Differentiable ℂ (splitBase p) := by
  exact (differentiable_const _).sub
    (((differentiable_const _).mul differentiable_id).neg.const_cpow
      (.inl (by exact_mod_cast p.1.2.ne_zero)))

theorem differentiable_remaining (p : SplitPrimes) :
    DifferentiableOn ℂ (remainingSplit p) {z : ℂ | (1 / 3 : ℝ) < z.re} := by
  have hp : Differentiable ℂ (fun z : ℂ => (p.1 : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (.inl (by exact_mod_cast p.1.2.ne_zero))
  exact (((differentiable_const _).sub ((differentiable_const _).mul (hp.pow 2))).add
    ((differentiable_const _).mul (hp.pow 3))).differentiableOn.div
      (((differentiable_const _).sub (hp.pow 2)).pow 3).differentiableOn
      (fun z hz => pow_ne_zero _
        (remaining_denominator_ne_zero _ (inversePower_bound p.1 hz)))

theorem locally_uniform_inert : HasProdLocallyUniformlyOn inertFourth inertProduct
    {z : ℂ | (1 / 4 : ℝ) < z.re} := by
  apply locally_uniform_of_majorants (1 / 4) inertFourth
    (fun τ q => ‖(q.1 : ℂ) ^ (-(4 * (τ : ℂ)))‖)
  · intro τ hτ
    exact (summable_prime_power (z := 4 * (τ : ℂ))
      (by norm_num [Complex.mul_re]; linarith)).subtype (fun p => (p : ℕ) % 3 = 2)
  · intro τ _ q z hz
    simp only [inertFourth, sub_sub_cancel_left, norm_neg]
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos q.1.2.pos
    norm_num [Complex.mul_re]
    linarith
  · intro q
    exact (differentiable_inert q).continuous.continuousOn

theorem locally_uniform_splitBase : HasProdLocallyUniformlyOn splitBase splitProduct
    {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  apply locally_uniform_of_majorants (1 / 2) splitBase
    (fun τ p => ‖(p.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖)
  · intro τ hτ
    exact (summable_prime_power (z := 2 * (τ : ℂ))
      (by norm_num [Complex.mul_re]; linarith)).subtype (fun p => (p : ℕ) % 3 = 1)
  · intro τ _ p z hz
    simp only [splitBase, sub_sub_cancel_left, norm_neg]
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.1.2.pos
    norm_num [Complex.mul_re]
    linarith
  · intro p
    exact (differentiable_splitBase p).continuous.continuousOn

theorem locally_uniform_remaining : HasProdLocallyUniformlyOn remainingSplit remainingProduct
    {z : ℂ | (1 / 3 : ℝ) < z.re} := by
  apply locally_uniform_of_majorants (1 / 3) remainingSplit
    (fun τ p => 384 * ‖(p.1 : ℂ) ^ (-(3 * (τ : ℂ)))‖)
  · intro τ hτ
    exact ((summable_prime_power (z := 3 * (τ : ℂ))
      (by norm_num [Complex.mul_re]; linarith)).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 384
  · intro τ hτ p z hz
    have h := remaining_deviation_bound _ (inversePower_bound p.1 (hτ.trans_le hz))
    rw [← norm_pow, ← HeightZetaCorrectionProduct.primePower_three] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.1.2.pos
        (by norm_num [Complex.mul_re]; linarith)) (by norm_num))
  · intro p
    exact (differentiable_remaining p).continuousOn

theorem differentiableOn_inertProduct :
    DifferentiableOn ℂ inertProduct {z : ℂ | (1 / 4 : ℝ) < z.re} :=
  locally_uniform_inert.differentiableOn
    (Filter.Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun q _ => (differentiable_inert q).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem differentiableOn_splitProduct :
    DifferentiableOn ℂ splitProduct {z : ℂ | (1 / 2 : ℝ) < z.re} :=
  locally_uniform_splitBase.differentiableOn
    (Filter.Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun p _ => (differentiable_splitBase p).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem differentiableOn_remainingProduct :
    DifferentiableOn ℂ remainingProduct {z : ℂ | (1 / 3 : ℝ) < z.re} :=
  locally_uniform_remaining.differentiableOn
    (Filter.Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun p _ => differentiable_remaining p)
    (isOpen_lt continuous_const Complex.continuous_re)

end Cubic.PoissonSummation.HeightZetaContinuationFactors
