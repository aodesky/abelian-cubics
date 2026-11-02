import Cubic.Analysis.GaussianMeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The reflected Cauchy kernel has uniformly bounded mass as its pole approaches
 the critical line. Fixed-δ integrability uses the existing Gaussian majorants. -/
noncomputable section
namespace Cubic.Analysis.PoissonGaussianWeight
open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData Cubic.Analysis.MeanValueExtension

/-- Gaussian-damped Poisson kernel (without the normalizing factor π). -/
def weight (δ x : ℝ) : ℝ := δ / (δ ^ 2 + x ^ 2) * Real.exp (-x ^ 2)

lemma denominator_pos {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 < δ ^ 2 + x ^ 2 := by
  positivity

lemma nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 ≤ weight δ x := by
  unfold weight; positivity

lemma continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (weight δ) := by
  unfold weight
  exact (continuous_const.div (by fun_prop) (fun x => (denominator_pos hδ x).ne')).mul
    (by fun_prop)

lemma le_gauss {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    weight δ x ≤ δ⁻¹ * Real.exp (-x ^ 2) := by
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [div_le_iff₀ (denominator_pos hδ x)]
  have h := mul_nonneg (inv_pos.mpr hδ).le (sq_nonneg x)
  have he : δ⁻¹ * δ ^ 2 = δ := by field_simp
  nlinarith

lemma integrable_mul {δ t : ℝ} (hδ : 0 < δ) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hg : Integrable fun v : ℝ => Real.exp (-(v - t) ^ 2) * φ v) :
    Integrable fun v : ℝ => weight δ (v - t) * φ v := by
  refine Integrable.mono' (hg.norm.const_mul δ⁻¹)
    (((continuous hδ).comp (by fun_prop)).mul hc).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Real.norm_of_nonneg (nonneg hδ _), norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc weight δ (v - t) * ‖φ v‖ ≤ (δ⁻¹ * Real.exp (-(v - t) ^ 2)) * ‖φ v‖ :=
      mul_le_mul_of_nonneg_right (le_gauss hδ _) (norm_nonneg _)
    _ = _ := by ring

lemma integrable_weight {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Integrable fun v : ℝ => weight δ (v - t) := by
  refine Integrable.mono' ((integrable_gauss_shift t).const_mul δ⁻¹)
    ((continuous hδ).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_of_nonneg (nonneg hδ _)]
  exact le_gauss hδ _

lemma mass_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (∫ v : ℝ, weight δ (v - t)) ≤ Real.pi := by
  let p : ℝ → ℝ := fun x => δ⁻¹ * (1 + (x / δ) ^ 2)⁻¹
  have hp : ∀ x : ℝ, p x = δ / (δ ^ 2 + x ^ 2) := by
    intro x
    dsimp [p]
    field_simp
    <;> ring
  have hip : Integrable p := (integrable_inv_one_add_sq.comp_div hδ.ne').const_mul _
  have hit : Integrable fun v : ℝ => p (v - t) := hip.comp_sub_right t
  have hi : (∫ v : ℝ, p (v - t)) = Real.pi := by
    rw [integral_sub_right_eq_self]
    dsimp [p]
    rw [integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) δ, integral_univ_inv_one_add_sq,
      abs_of_pos hδ, smul_eq_mul]
    field_simp
  rw [← hi]
  apply integral_mono (integrable_weight hδ t) hit
  intro v
  change weight δ (v - t) ≤ p (v - t)
  rw [hp, weight]
  have he : Real.exp (-(v - t) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (v-t)])
  exact mul_le_of_le_one_right (by positivity) he

lemma integrable_zeta (hG : Growth) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Integrable fun v : ℝ => weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ :=
  integrable_mul hδ continuous_zetaE_half.norm (integrable_gauss_zetaE hG t)

lemma integrable_zeta_sq (hG : Growth) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Integrable fun v : ℝ => weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 :=
  integrable_mul hδ (continuous_zetaE_half.norm.pow 2) (integrable_gauss_zetaE_sq hG t)

lemma cauchy_schwarz (hG : Growth) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∫ v : ℝ, weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ≤
      Real.sqrt (1 + ∫ v : ℝ, weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) *
        (Real.pi + 1) / 2 := by
  set I₂ := ∫ v : ℝ, weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun v => mul_nonneg (nonneg hδ _) (sq_nonneg _)
  set l := Real.sqrt (1 + I₂)
  have hl : 0 < l := Real.sqrt_pos.mpr (by linarith)
  have hl2 : l ^ 2 = 1 + I₂ := Real.sq_sqrt (by linarith)
  have hint : Integrable fun v : ℝ => (l * weight δ (v - t) +
      weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 / l) / 2 :=
    ((((integrable_weight hδ t).const_mul l).add
      ((integrable_zeta_sq hG hδ t).div_const l)).div_const 2)
  calc ∫ v : ℝ, weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
      ≤ ∫ v : ℝ, (l * weight δ (v - t) +
          weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 / l) / 2 := by
        refine integral_mono (integrable_zeta hG hδ t) hint fun v => ?_
        set e := weight δ (v - t)
        set y := ‖zetaE ((1 / 2 : ℂ) + v * I)‖
        have he : 0 ≤ e := nonneg hδ _
        have eq : (l * e + e * y ^ 2 / l) / 2 - e * y = e * (l - y) ^ 2 / (2 * l) := by
          field_simp
          ring
        have : 0 ≤ e * (l - y) ^ 2 / (2 * l) := by positivity
        linarith
    _ = (l * (∫ v : ℝ, weight δ (v - t)) + I₂ / l) / 2 := by
        rw [integral_div, integral_add ((integrable_weight hδ t).const_mul l)
          ((integrable_zeta_sq hG hδ t).div_const l), integral_const_mul, integral_div]
    _ ≤ l * (Real.pi + 1) / 2 := by
        have : I₂ / l ≤ l := by
          rw [div_le_iff₀ hl]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left (mass_le hδ t) hl.le
        linarith

lemma average_swap (hG : Growth) {δ : ℝ} (hδ : 0 < δ) {U : ℝ} (hU : 2 ≤ U) :
    IntervalIntegrable (fun t : ℝ => ∫ v : ℝ, weight δ (v - t) *
        ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) volume U (2 * U) ∧
      Integrable (fun v : ℝ => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 *
        ∫ t in U..2 * U, weight δ (v - t)) ∧
      ∫ t in U..2 * U, (∫ v : ℝ, weight δ (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) =
        ∫ v : ℝ, ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 *
          ∫ t in U..2 * U, weight δ (v - t) := by
  set Z : ℝ → ℝ := fun v => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 with hZdef
  have hZc : Continuous Z := continuous_zetaE_half.norm.pow 2
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  have hZM : ∀ v, |Z v| ≤ M * (1 + |v|) ^ 8 := fun v => by
    rw [abs_of_nonneg (by positivity)]; exact (hM v).2
  have hUU : U ≤ 2 * U := by linarith
  set μ : Measure ℝ := volume.restrict (Ioc U (2 * U))
  set f : ℝ → ℝ → ℝ := fun t v => weight δ (v - t) * Z v
  have hint : Integrable (Function.uncurry f) (μ.prod volume) := by
    have hf : Integrable (fun t : ℝ => Real.exp (t ^ 2)) μ :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (t ^ 2)).integrableOn_Icc
        (a := U) (b := 2 * U)).mono_set Ioc_subset_Icc_self
    have hg := integrable_mul_gauss hZc hZM (b := 1 / 2) (by norm_num)
    refine Integrable.mono' ((hf.mul_prod hg).const_mul δ⁻¹) ?_ (Eventually.of_forall fun p => ?_)
    · exact (((continuous hδ).comp (by fun_prop)).mul (hZc.comp continuous_snd)).aestronglyMeasurable
    · simp only [Function.uncurry, f]
      have hZ0 : 0 ≤ Z p.2 := by positivity
      rw [norm_mul, Real.norm_of_nonneg (nonneg hδ _), Real.norm_of_nonneg hZ0]
      have := gauss_shift_le p.1 p.2
      calc weight δ (p.2 - p.1) * Z p.2
          ≤ (δ⁻¹ * Real.exp (-(p.2 - p.1) ^ 2)) * Z p.2 :=
            mul_le_mul_of_nonneg_right (le_gauss hδ _) hZ0
        _ ≤ δ⁻¹ * (Real.exp (p.1 ^ 2) * Real.exp (-(1 / 2) * p.2 ^ 2)) * Z p.2 := by
            gcongr
        _ = _ := by ring
  have hswap := integral_integral_swap hint
  have hinner : ∀ v : ℝ, ∫ t, f t v ∂μ = Z v * ∫ t in U..2 * U, weight δ (v - t) := by
    intro v
    simp only [f, μ]
    rw [integral_mul_const, intervalIntegral.integral_of_le hUU, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hUU]
    exact hint.integral_prod_left
  · have := hint.integral_prod_right
    simp only [Function.uncurry] at this
    exact this.congr (Eventually.of_forall hinner)
  · rw [intervalIntegral.integral_of_le hUU]
    change ∫ t, ∫ v, f t v ∂volume ∂μ = _
    rw [hswap]
    exact integral_congr_ae (Eventually.of_forall hinner)

end Cubic.Analysis.PoissonGaussianWeight
