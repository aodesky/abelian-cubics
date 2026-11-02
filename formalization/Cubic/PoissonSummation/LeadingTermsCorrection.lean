import Cubic.PoissonSummation.LeadingTermsData
import Cubic.PoissonSummation.HeightZetaContinuationFactorization

/-!
# Holomorphy and positivity of the correction product

The variable here is the height-series variable `s=2z` in `prop:leadingTerms`. Absolute convergence
and positivity of every real factor are both used to prove `E_paper(1)>0`:
positivity of the factors alone would not exclude a zero infinite product.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsCorrection

open FiniteEulerProduct LeadingTermsData

theorem half_re {s : ℂ} (hs : 1 < s.re) : (1 / 2 : ℝ) < (s / 2).re := by
  norm_num [Complex.div_re]
  linarith

theorem inert_absolute (s : ℂ) (hs : 1 < s.re) :
    Summable (fun q : InertPrimes => ‖HeightZetaCorrectionProduct.inert q (s / 2) - 1‖) :=
  HeightZetaCorrectionProduct.absolute_inert _ (half_re hs)

theorem split_absolute (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : SplitPrimes => ‖HeightZetaCorrectionProduct.split p (s / 2) - 1‖) :=
  HeightZetaCorrectionProduct.absolute_split _ (half_re hs)

theorem differentiableOn_correction :
    DifferentiableOn ℂ correction {s : ℂ | 1 < s.re} := by
  intro s hs
  have hd := HeightZetaContinuationFactorization.differentiableOn_correction.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_re hs))
  have hc : DifferentiableAt ℂ (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2) s := by
    fun_prop
  exact (hc.mul (hd.comp s
    (show DifferentiableAt ℂ (fun s : ℂ => s / 2) s by fun_prop))).differentiableWithinAt

def inertReal (q : InertPrimes) : ℝ := 1 - (q.1 : ℝ)⁻¹ ^ 2

def splitReal (p : SplitPrimes) : ℝ :=
  (1 - (p.1 : ℝ)⁻¹) ^ 2 * (1 + 2 * (p.1 : ℝ)⁻¹)

theorem prime_inv_lt_one (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 := by
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

theorem inertReal_pos (q : InertPrimes) : 0 < inertReal q := by
  have h := prime_inv_lt_one q.1
  have h0 : 0 ≤ (q.1 : ℝ)⁻¹ := by positivity
  dsimp [inertReal]
  nlinarith

theorem splitReal_pos (p : SplitPrimes) : 0 < splitReal p := by
  apply mul_pos
  · exact sq_pos_of_pos (sub_pos.mpr (prime_inv_lt_one p.1))
  · positivity

theorem inert_one (q : InertPrimes) :
    HeightZetaCorrectionProduct.inert q 1 = (inertReal q : ℂ) := by
  simp [HeightZetaCorrectionProduct.inert, inertReal, Complex.cpow_neg, inv_pow]

theorem split_one (p : SplitPrimes) :
    HeightZetaCorrectionProduct.split p 1 = (splitReal p : ℂ) := by
  rw [HeightZetaCorrectionProduct.split_eq_polynomial, splitCorrection_factor]
  simp [splitReal, Complex.cpow_neg]

private theorem real_product_positive {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) (ha : Summable (fun i => ‖f i - 1‖)) : 0 < ∏' i, f i := by
  have hl : Summable (fun i => Real.log (f i)) := by
    simpa using Real.summable_log_one_add_of_summable ha.of_norm
  rw [← Real.rexp_tsum_eq_tprod hf hl]
  exact Real.exp_pos _

private theorem real_product_cast {ι : Type*} (f : ι → ℝ)
    (ha : Summable (fun i => ‖f i - 1‖)) :
    (∏' i, (f i : ℂ)) = ((∏' i, f i : ℝ) : ℂ) := by
  have hm : Multipliable f := by
    simpa using multipliable_one_add_of_summable ha
  exact (hm.map_tprod Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal).symm

theorem inertReal_absolute : Summable (fun q : InertPrimes => ‖inertReal q - 1‖) := by
  have h := HeightZetaCorrectionProduct.absolute_inert 1 (by norm_num)
  simp only [inert_one] at h
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real] using h

theorem splitReal_absolute : Summable (fun p : SplitPrimes => ‖splitReal p - 1‖) := by
  have h := HeightZetaCorrectionProduct.absolute_split 1 (by norm_num)
  simp only [split_one] at h
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real] using h

theorem correction_two : correction 2 =
    (((4 / 9 : ℝ) * (∏' q : InertPrimes, inertReal q) *
      (∏' p : SplitPrimes, splitReal p) : ℝ) : ℂ) := by
  simp only [correction, div_self (by norm_num : (2 : ℂ) ≠ 0),
    HeightZetaCorrectionProduct.value, inert_one, split_one,
    real_product_cast _ inertReal_absolute, real_product_cast _ splitReal_absolute]
  push_cast
  norm_num [Complex.cpow_neg]
  ring

theorem correction_two_real : (correction 2).im = 0 := by
  rw [correction_two]
  rfl

theorem correction_two_pos : 0 < (correction 2).re := by
  rw [correction_two, Complex.ofReal_re]
  exact mul_pos (mul_pos (by norm_num)
    (real_product_positive _ inertReal_pos inertReal_absolute))
    (real_product_positive _ splitReal_pos splitReal_absolute)

theorem correction_two_ne_zero : correction 2 ≠ 0 := by
  intro h
  have := correction_two_pos
  simp [h] at this

end Cubic.PoissonSummation.LeadingTermsCorrection
