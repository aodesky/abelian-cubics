import Cubic.PoissonSummation.HeightZetaContinuationFactors
import Cubic.PoissonSummation.SplitProductContinuation

/-!
# Factoring the height correction through `L(2z,χ)`

All product regroupings are made only after proving convergence. The resulting
factorization supplies holomorphy on `Re z > 1/2` by the paper's argument,
using the fourth-power inert product and the degree-three remaining split
product on their larger convergence regions.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContinuationFactorization

open Filter FiniteEulerProduct HeightZetaFormulaData HeightZetaEulerExtraction
open HeightZetaContinuationFactors
open scoped Topology

def factorized (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction QuadraticDirichletCharacter.character (2 * z) *
    inertProduct z * splitProduct z ^ 4 * remainingProduct z

def continuedFactorized (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction QuadraticDirichletCharacter.character (2 * z) *
    inertProduct z * (SplitProductContinuation.value z)⁻¹ * remainingProduct z

theorem inert_identity (q : InertPrimes) (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    inertCorrection q (2 * z) * inertFourth q z = HeightZetaCorrectionProduct.inert q z := by
  have h2 : 1 < (2 * z).re := by norm_num [Complex.mul_re]; linarith
  have hb := Complex.norm_prime_cpow_le_one_half q.1 h2
  have hp : 1 + (q.1 : ℂ) ^ (-(2 * z)) ≠ 0 := by
    intro h
    have he := eq_neg_of_add_eq_zero_right h
    rw [he] at hb
    norm_num at hb
  have h4 : (q.1 : ℂ) ^ (-(4 * z)) = ((q.1 : ℂ) ^ (-(2 * z))) ^ 2 := by
    simpa only [show (2 : ℂ) * (2 * z) = 4 * z by ring] using
      HeightZetaCorrectionProduct.primePower_two q.1 (2 * z)
  unfold inertCorrection inertFourth HeightZetaCorrectionProduct.inert
  rw [h4]
  field_simp [hp]
  ring

theorem split_identity (p : SplitPrimes) (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹ * splitBase p z ^ 4 * remainingSplit p z =
      HeightZetaCorrectionProduct.split p z := by
  have hd := remaining_denominator_ne_zero _
    (inversePower_bound p.1 (by linarith : (1 / 3 : ℝ) < z.re))
  unfold splitBase remainingSplit remainingCorrection HeightZetaCorrectionProduct.split
  rw [HeightZetaCorrectionProduct.primePower_two, HeightZetaCorrectionProduct.primePower_three]
  field_simp [hd]

theorem correction_eq_factorized (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    HeightZetaCorrectionProduct.value z = factorized z := by
  have h2 : 1 < (2 * z).re := by norm_num [Complex.mul_re]; linarith
  have hi := ((inert_product_multipliable (2 * z) h2).hasProd.mul
    (multipliable_inert z (by linarith)).hasProd).congr_fun
      (fun q => (inert_identity q z hz).symm)
  have hie := hi.unique (HeightZetaCorrectionProduct.convergent_inert z hz).hasProd
  have hbase := (multipliable_splitBase z hz).hasProd
  have hpow : HasProd (fun p : SplitPrimes => splitBase p z ^ 4)
      ((∏' p : SplitPrimes, splitBase p z) ^ 4) := by
    simpa [pow_succ, mul_assoc] using ((hbase.mul hbase).mul (hbase.mul hbase))
  have hs := (((zeta_split_multipliable (2 * z) h2).hasProd.mul
    hpow).mul
      (multipliable_remaining z (by linarith)).hasProd).congr_fun
        (fun p => (split_identity p z hz).symm)
  have hse := hs.unique (HeightZetaCorrectionProduct.convergent_split z hz).hasProd
  unfold HeightZetaCorrectionProduct.value factorized inertProduct splitProduct remainingProduct
  rw [← hie, ← hse, QuadraticLEulerProduct.product (2 * z) h2]
  ring

theorem correction_eq_continuedFactorized (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    HeightZetaCorrectionProduct.value z = continuedFactorized z := by
  rw [correction_eq_factorized z hz, continuedFactorized,
    SplitProductContinuation.inverse_agreement z hz]
  rfl

theorem differentiableOn_factorized :
    DifferentiableOn ℂ factorized {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  intro z hz
  change (1 / 2 : ℝ) < z.re at hz
  have hL := (QuadraticDirichletCharacter.differentiable_LFunction (2 * z)).comp z
    (show DifferentiableAt ℂ (fun w : ℂ => 2 * w) z by fun_prop)
  have hi := differentiableOn_inertProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 4 : ℝ) < z.re by linarith))
  have hs := differentiableOn_splitProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have hr := differentiableOn_remainingProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 3 : ℝ) < z.re by linarith))
  exact (((hL.mul hi).mul (hs.pow 4)).mul hr).differentiableWithinAt

theorem differentiableOn_continuedFactorized :
    DifferentiableOn ℂ continuedFactorized {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  intro z hz
  change (1 / 2 : ℝ) < z.re at hz
  have hL := (QuadraticDirichletCharacter.differentiable_LFunction (2 * z)).comp z
    (show DifferentiableAt ℂ (fun w : ℂ => 2 * w) z by fun_prop)
  have hi := differentiableOn_inertProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 4 : ℝ) < z.re by linarith))
  have hs := SplitProductContinuation.differentiableOn_inverse.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have hr := differentiableOn_remainingProduct.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 3 : ℝ) < z.re by linarith))
  exact (((hL.mul hi).mul hs).mul hr).differentiableWithinAt

/-- Holomorphy of the original correction product now follows from the
paper's `L(2z,χ)` factorization, rather than direct correction majorants. -/
theorem differentiableOn_correction :
    DifferentiableOn ℂ HeightZetaCorrectionProduct.value
      {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  intro z hz
  have hd := differentiableOn_continuedFactorized.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have he : HeightZetaCorrectionProduct.value =ᶠ[𝓝 z] continuedFactorized := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
      with w hw using correction_eq_continuedFactorized w hw
  exact (hd.congr_of_eventuallyEq he).differentiableWithinAt

end Cubic.PoissonSummation.HeightZetaContinuationFactorization
