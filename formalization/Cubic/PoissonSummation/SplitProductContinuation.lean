import Cubic.PoissonSummation.HeightZetaContinuationFactors
import Cubic.PoissonSummation.RiemannZetaMeromorphy
import Cubic.PoissonSummation.QuadraticZetaRegularization
import Cubic.PoissonSummation.AnalyticLaurent

/-!
# Continuation and boundary behavior of the reciprocal split product

The paper's reciprocal fourth-power product is continued by
`((1-3^(-2z)) ζ(2z) L(2z,χ) I₄(z))²`. The expression is meromorphic
on `Re z > 1/4`, has exact pole order two at `z=1/2`, and has no zeros
on `Re z=1/2` away from that pole. Its inverse is holomorphic on the
open half-plane needed by the height continuation.
-/

noncomputable section

namespace Cubic.PoissonSummation.SplitProductContinuation

open Filter FiniteEulerProduct HeightZetaFormulaData HeightZetaEulerExtraction
open HeightZetaContinuationFactors
open scoped Topology

def value (z : ℂ) : ℂ :=
  ((1 - (3 : ℂ) ^ (-(2 * z))) * QuadraticZetaRegularization.value (2 * z) *
    inertProduct z) ^ 2

def numerator (z : ℂ) : ℂ :=
  ((1 - (3 : ℂ) ^ (-(2 * z))) * QuadraticZetaRegularization.regular (2 * z) *
    inertProduct z) ^ 2 / 4

theorem primePower_norm_lt_one (p : Nat.Primes) (z : ℂ) (hz : 0 < z.re) :
    ‖(p : ℂ) ^ (-z)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)

theorem primeFactor_ne_zero (p : Nat.Primes) (z : ℂ) (hz : 0 < z.re) :
    1 - (p : ℂ) ^ (-z) ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  have hn := primePower_norm_lt_one p z hz
  rw [← he, norm_one] at hn
  exact (lt_irrefl _ hn)

set_option maxHeartbeats 600000 in
theorem inertProduct_ne_zero (z : ℂ) (hz : (1 / 4 : ℝ) < z.re) :
    inertProduct z ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (R := ℂ) (ι := InertPrimes)
    (f := fun q : InertPrimes => inertFourth q z - 1)
    (fun q => by
      simp only [add_sub_cancel]
      exact primeFactor_ne_zero q.1 (4 * z) (by norm_num [Complex.mul_re]; linarith))
    (HeightZetaContinuationFactors.absolute_inert z hz)
  simpa only [add_sub_cancel, inertProduct] using h

theorem zeta_L_cancellation (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    (1 - (3 : ℂ) ^ (-(2 * z))) * QuadraticZetaRegularization.value (2 * z) *
        inertProduct z =
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹) ^ 2 := by
  have h2 : 1 < (2 * z).re := by norm_num [Complex.mul_re]; linarith
  have hlocal (q : InertPrimes) :
      (1 - (q.1 : ℂ) ^ (-(2 * z)))⁻¹ * inertCorrection q (2 * z) * inertFourth q z = 1 := by
    have hm := Complex.one_sub_prime_cpow_ne_zero q.1.2 h2
    have hp : 1 + (q.1 : ℂ) ^ (-(2 * z)) ≠ 0 := by
      have hb := Complex.norm_prime_cpow_le_one_half q.1 h2
      intro he
      rw [eq_neg_of_add_eq_zero_right he] at hb
      norm_num at hb
    have h4 : (q.1 : ℂ) ^ (-(4 * z)) = ((q.1 : ℂ) ^ (-(2 * z))) ^ 2 := by
      simpa only [show (2 : ℂ) * (2 * z) = 4 * z by ring] using
        HeightZetaCorrectionProduct.primePower_two q.1 (2 * z)
    unfold inertCorrection inertFourth
    rw [h4]
    field_simp [hm, hp]
    ring
  have hc := (((zeta_inert_multipliable (2 * z) h2).hasProd.mul
    (inert_product_multipliable (2 * z) h2).hasProd).mul
      (multipliable_inert z (by linarith)).hasProd).congr_fun
        (fun q => (hlocal q).symm)
  have he := hc.unique (hasProd_one : HasProd (fun _ : InertPrimes => (1 : ℂ)) 1)
  unfold QuadraticZetaRegularization.value inertProduct
  rw [← mul_assoc, ← zeta_without_three (2 * z) h2,
    QuadraticLEulerProduct.product (2 * z) h2]
  calc
    _ = ((∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-(2 * z)))⁻¹) *
          (∏' q : InertPrimes, inertCorrection q (2 * z)) *
          (∏' q : InertPrimes, inertFourth q z)) *
        (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹) ^ 2 := by ring
    _ = _ := by rw [he, one_mul]

theorem splitProduct_ne_zero (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    splitProduct z ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun p : SplitPrimes => splitBase p z - 1)
    (fun p => by
      simp only [add_sub_cancel]
      exact primeFactor_ne_zero p.1 (2 * z) (by norm_num [Complex.mul_re]; linarith))
    (absolute_splitBase z hz)
  simpa only [add_sub_cancel, splitProduct] using h

theorem inverse_product (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹) = (splitProduct z)⁻¹ := by
  have h2 : 1 < (2 * z).re := by norm_num [Complex.mul_re]; linarith
  have hp := ((multipliable_splitBase z hz).hasProd.mul
    (zeta_split_multipliable (2 * z) h2).hasProd).congr_fun (fun p => by
      change (1 : ℂ) = splitBase p z * (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹
      unfold splitBase
      rw [mul_inv_cancel₀ (Complex.one_sub_prime_cpow_ne_zero p.1.2 h2)])
  have he := hp.unique (hasProd_one : HasProd (fun _ : SplitPrimes => (1 : ℂ)) 1)
  change splitProduct z * _ = 1 at he
  have hn := splitProduct_ne_zero z hz
  apply mul_left_cancel₀ hn
  rw [he, mul_inv_cancel₀ hn]

theorem agreement (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    value z = (splitProduct z)⁻¹ ^ 4 := by
  rw [value, zeta_L_cancellation z hz, inverse_product z hz]
  ring

theorem inverse_agreement (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    (value z)⁻¹ = splitProduct z ^ 4 := by
  rw [agreement z hz, ← inv_pow, inv_inv]

theorem differentiable_prefactor :
    Differentiable ℂ (fun w : ℂ => 1 - (3 : ℂ) ^ (-(2 * w))) :=
  (differentiable_const _).sub
    (((differentiable_const _).mul differentiable_id).neg.const_cpow (.inl (by norm_num)))

theorem meromorphic : MeromorphicOn value {z : ℂ | (1 / 4 : ℝ) < z.re} := by
  intro z hz
  change (1 / 4 : ℝ) < z.re at hz
  have hthree := differentiable_prefactor.analyticAt z
  have hζ := (RiemannZetaMeromorphy.meromorphicAt (2 * z)
    (by norm_num [Complex.mul_re]; linarith)).comp_analyticAt
      (g := fun w : ℂ => 2 * w) (by fun_prop)
  have hL : AnalyticAt ℂ
      (fun w : ℂ => DirichletCharacter.LFunction QuadraticDirichletCharacter.character (2 * w)) z :=
    (QuadraticDirichletCharacter.differentiable_LFunction.analyticAt (2 * z)).comp
      (f := fun w : ℂ => 2 * w) (by fun_prop)
  have hi := differentiableOn_inertProduct.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  change MeromorphicAt (fun w : ℂ =>
    ((1 - (3 : ℂ) ^ (-(2 * w))) *
      (riemannZeta (2 * w) *
        DirichletCharacter.LFunction QuadraticDirichletCharacter.character (2 * w)) *
      inertProduct w) ^ 2) z
  simpa only [Function.comp_def, mul_assoc] using
    (((hthree.meromorphicAt.fun_mul hζ).fun_mul hL.meromorphicAt).fun_mul
      hi.meromorphicAt).fun_pow 2

theorem nonzero (z : ℂ) (hz : (1 / 2 : ℝ) ≤ z.re) : value z ≠ 0 := by
  have h2 : 1 ≤ (2 * z).re := by norm_num [Complex.mul_re]; linarith
  unfold value QuadraticZetaRegularization.value
  exact pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (primeFactor_ne_zero primeThree (2 * z)
      (by norm_num [Complex.mul_re]; linarith))
      (mul_ne_zero (riemannZeta_ne_zero_of_one_le_re h2)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re
          QuadraticDirichletCharacter.character
          (Or.inl QuadraticDirichletCharacter.character_ne_one) h2)))
      (inertProduct_ne_zero z (by linarith)))

theorem boundary_nonzero (z : ℂ) (hz : z.re = (1 / 2 : ℝ)) (_hne : z ≠ 1 / 2) :
    value z ≠ 0 := nonzero z hz.ge

theorem numerator_analytic (z : ℂ) (hz : (1 / 4 : ℝ) < z.re) :
    AnalyticAt ℂ numerator z := by
  have hthree := differentiable_prefactor.analyticAt z
  have hR : AnalyticAt ℂ (fun w : ℂ => QuadraticZetaRegularization.regular (2 * w)) z :=
    (QuadraticZetaRegularization.differentiable_regular.analyticAt (2 * z)).comp
      (f := fun w : ℂ => 2 * w) (by fun_prop)
  have hi := differentiableOn_inertProduct.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  exact (((hthree.fun_mul hR).fun_mul hi).fun_pow 2).fun_div analyticAt_const (by norm_num)

theorem numerator_half_ne_zero : numerator (1 / 2) ≠ 0 := by
  unfold numerator
  norm_num only [mul_one_div, div_self (by norm_num : (2 : ℂ) ≠ 0)]
  exact div_ne_zero (pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (primeFactor_ne_zero primeThree 1 (by norm_num))
      QuadraticZetaRegularization.regular_one_ne_zero)
      (inertProduct_ne_zero (1 / 2) (by norm_num)))) (by norm_num)

theorem value_eq_quotient (z : ℂ) (hz : z ≠ 1 / 2) :
    value z = numerator z / (z - 1 / 2) ^ 2 := by
  have h2 : 2 * z ≠ 1 := by
    intro h
    apply hz
    linear_combination h / 2
  have hr := QuadraticZetaRegularization.regular_eq (2 * z) h2
  have hden : z - (1 / 2 : ℂ) = (2 * z - 1) / 2 := by ring
  unfold value numerator
  rw [hr, hden]
  field_simp [sub_ne_zero.mpr h2]
  ring

theorem pole_order : meromorphicOrderAt value (1 / 2) = (-2 : ℤ) :=
  AnalyticLaurent.order_of_nonzero_numerator (numerator_analytic (1 / 2) (by norm_num))
    numerator_half_ne_zero (by
      filter_upwards [self_mem_nhdsWithin] with z hz using value_eq_quotient z hz)

theorem differentiableOn_inverse :
    DifferentiableOn ℂ (fun z => (value z)⁻¹) {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  intro z hz
  change (1 / 2 : ℝ) < z.re at hz
  have h2 : 2 * z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [Complex.mul_re] at this
    linarith
  have hthree := differentiable_prefactor z
  have hξ := (QuadraticZetaRegularization.differentiableAt_value (2 * z) h2).comp z
    (show DifferentiableAt ℂ (fun w : ℂ => 2 * w) z by fun_prop)
  have hi := differentiableOn_inertProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 4 : ℝ) < z.re by linarith))
  exact ((((hthree.mul hξ).mul hi).pow 2).inv (nonzero z hz.le)).differentiableWithinAt

end Cubic.PoissonSummation.SplitProductContinuation
