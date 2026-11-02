import Cubic.BoxAsymptotic.HeckeCosineAFE
import Cubic.BoxAsymptotic.HeckeWeightVariation

/-! Comparing the textbook analytic conductor with the norm scale in the
moment proof. These inequalities discharge the cubic specialization of the
generic weight estimates; their constants are uniform in the angular mode.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeCosineWeights

open Cubic.Analysis.GammaAFEData
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeCosineAFE
open MeasureTheory

def modeLength (k : ℤ) (u : ℂ) : ℝ := 1 + gammaShift k + |u.im|

theorem finite_scale (k : ℤ) :
    1 ≤ 2 * Real.pi * conductorScale k ∧ 2 * Real.pi * conductorScale k ≤ 6 := by
  unfold conductorScale
  have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  split_ifs
  · rw [mul_div_cancel₀ _ hpi]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    constructor <;> nlinarith
  · rw [mul_div_cancel₀ _ hpi]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)
    have hn := Real.sqrt_nonneg (27 : ℝ)
    constructor <;> nlinarith

theorem length_comparison {k : ℤ} (hk : 2 ≤ k) (u : ℂ)
    (hu : 1 / 4 ≤ u.re) (hu' : u.re ≤ 3 / 4) :
    modeLength k u / 2 ≤ length (conductorScale k) (gammaShift k) u ∧
      length (conductorScale k) (gammaShift k) u ≤ 30 * modeLength k u := by
  set κ := gammaShift k
  set W := modeLength k u
  have hκ : 1 ≤ κ := gammaShift_ge_one hk
  have hW : 2 ≤ W := by dsimp [W, modeLength]; linarith [abs_nonneg u.im]
  have ha := Complex.abs_re_le_norm (u + (κ : ℂ))
  have hb := Complex.abs_im_le_norm (u + (κ : ℂ))
  have ha' := Complex.abs_re_le_norm (u + (κ : ℂ) + 1)
  have hb' := Complex.abs_im_le_norm (u + (κ : ℂ) + 1)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re,
    Complex.add_im, Complex.ofReal_im, Complex.one_im, add_zero] at ha hb ha' hb'
  rw [abs_of_nonneg (by linarith : 0 ≤ u.re + κ)] at ha
  rw [abs_of_nonneg (by linarith : 0 ≤ u.re + κ + 1)] at ha'
  have hna := Complex.norm_le_abs_re_add_abs_im (u + (κ : ℂ))
  have hnb := Complex.norm_le_abs_re_add_abs_im (u + (κ : ℂ) + 1)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re,
    Complex.add_im, Complex.ofReal_im, Complex.one_im, add_zero] at hna hnb
  rw [abs_of_nonneg (by linarith : 0 ≤ u.re + κ)] at hna
  rw [abs_of_nonneg (by linarith : 0 ≤ u.re + κ + 1)] at hnb
  have hWe : W = 1 + κ + |u.im| := rfl
  have hal : W / 2 ≤ ‖u + (κ : ℂ)‖ + 3 := by linarith
  have hbl : W / 2 ≤ ‖u + (κ : ℂ) + 1‖ + 3 := by linarith
  have hau : ‖u + (κ : ℂ)‖ + 3 ≤ 5 * W := by linarith
  have hbu : ‖u + (κ : ℂ) + 1‖ + 3 ≤ 5 * W := by linarith
  set R := Real.sqrt ((‖u + (κ : ℂ)‖ + 3) * (‖u + (κ : ℂ) + 1‖ + 3))
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (‖u + (κ : ℂ)‖ + 3) * (‖u + (κ : ℂ) + 1‖ + 3) :=
    Real.sq_sqrt (by positivity)
  have hRl : W / 2 ≤ R := by
    have hp := mul_le_mul hal hbl (by linarith : 0 ≤ W / 2) (by positivity)
    nlinarith
  have hRu : R ≤ 5 * W := by
    have hp := mul_le_mul hau hbu (by positivity) (by linarith : 0 ≤ 5 * W)
    nlinarith
  obtain ⟨hq, hq'⟩ := finite_scale k
  change W / 2 ≤ (2 * Real.pi * conductorScale k) * R ∧
    (2 * Real.pi * conductorScale k) * R ≤ 30 * W
  constructor
  · exact hRl.trans (by nlinarith)
  · nlinarith

theorem small_rescale {x W L : ℝ} (hx : 0 < x) (hW : 0 < W) (hWL : W / 2 ≤ L) :
    (x / L) ^ (1 / 4 : ℝ) ≤ 2 * (x / W) ^ (1 / 4 : ℝ) := by
  have hL : 0 < L := by linarith
  have hd : x / L ≤ 2 * (x / W) := by
    apply (div_le_iff₀ hL).mpr
    field_simp
    nlinarith
  calc
    _ ≤ (2 * (x / W)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hd (by norm_num)
    _ = (2 : ℝ) ^ (1 / 4 : ℝ) * (x / W) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (x / W) ^ (1 / 4 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 4 : ℝ) ≤ 1)

theorem decay_rescale {x W L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hLW : L ≤ 30 * W) :
    (1 + x / L) ^ (-(3 : ℝ)) ≤ 27000 * (W / x) ^ 3 := by
  have hdiv : (1 + x / L)⁻¹ ≤ L / x := by
    calc
      _ ≤ (x / L)⁻¹ := inv_anti₀ (by positivity) (by linarith)
      _ = _ := inv_div _ _
  have hr : L / x ≤ 30 * (W / x) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hLW hx.le
  calc
    _ = ((1 + x / L)⁻¹) ^ 3 := by
      rw [Real.rpow_neg (show 0 ≤ 1 + x / L by positivity)]
      norm_num only [Real.rpow_ofNat]
      rw [inv_pow]
    _ ≤ (30 * (W / x)) ^ 3 := pow_le_pow_left₀ (by positivity) (hdiv.trans hr) 3
    _ = _ := by ring

theorem regular_on_interval {Q κ : ℝ} {u : ℂ} {a b : ℝ} (ha : 0 < a)
    (hd : DifferentiableOn ℝ (weight Q κ u) (Set.Ioi 0))
    (hc : ContinuousOn (deriv (weight Q κ u)) (Set.Ioi 0)) :
    (∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (weight Q κ u) x) ∧
      IntegrableOn (deriv (weight Q κ u)) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => ha.trans_le hx.1
  refine ⟨fun x hx => (hd x (hsub hx)).differentiableAt (isOpen_Ioi.mem_nhds (hsub hx)), ?_⟩
  exact (hc.mono hsub).integrableOn_Icc

/-- The actual cubic specialization of Proposition 5.4. The generic analytic
conductor is replaced by `1+|k|/2+|Im u|` using proved comparisons above. -/
theorem bounds (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (u : ℂ),
      2 ≤ k → 1 / 4 ≤ u.re → u.re ≤ 3 / 4 →
      let w := weight (conductorScale k) (gammaShift k) u
      DifferentiableOn ℝ w (Set.Ioi 0) ∧ ContinuousOn (deriv w) (Set.Ioi 0) ∧
      (∀ x > 0, ‖w x - 1‖ ≤ C * (x / modeLength k u) ^ (1 / 4 : ℝ)) ∧
      (∀ x > 0, x * ‖deriv w x‖ ≤ C * (x / modeLength k u) ^ (1 / 4 : ℝ)) ∧
      (∀ x > 0, ‖w x‖ ≤ C * (modeLength k u / x) ^ 3) ∧
      (∀ x > 0, x * ‖deriv w x‖ ≤ C * (modeLength k u / x) ^ 3) := by
  obtain ⟨C, hC, hb⟩ := hWeights
  refine ⟨27000 * C, mul_pos (by norm_num) hC, fun k u hk hu hu' => ?_⟩
  obtain ⟨hd, hc, hs, hs', hl, hl'⟩ := hb (conductorScale k) (gammaShift k) u
    (conductorScale_pos k) (gammaShift_ge_one hk) hu hu'
  obtain ⟨hlo, hhi⟩ := length_comparison hk u hu hu'
  have hW : 0 < modeLength k u := by
    dsimp [modeLength]
    linarith [gammaShift_ge_one hk, abs_nonneg u.im]
  have hL : 0 < length (conductorScale k) (gammaShift k) u := by linarith
  have small (x b : ℝ) (hx : 0 < x)
      (h : b ≤ C * (x / length (conductorScale k) (gammaShift k) u) ^ (1 / 4 : ℝ)) :
      b ≤ 27000 * C * (x / modeLength k u) ^ (1 / 4 : ℝ) := by
    have hr := mul_le_mul_of_nonneg_left (small_rescale hx hW hlo) hC.le
    have hp : 0 ≤ C * (x / modeLength k u) ^ (1 / 4 : ℝ) := by positivity
    nlinarith
  have large (x b : ℝ) (hx : 0 < x)
      (h : b ≤ C * (1 + x / length (conductorScale k) (gammaShift k) u) ^ (-(3 : ℝ))) :
      b ≤ 27000 * C * (modeLength k u / x) ^ 3 := by
    have hr := mul_le_mul_of_nonneg_left (decay_rescale hx hL hhi) hC.le
    nlinarith
  exact ⟨hd, hc, fun x hx => small x _ hx (hs x hx), fun x hx => small x _ hx (hs' x hx),
    fun x hx => large x _ hx (hl x hx), fun x hx => large x _ hx (hl' x hx)⟩

end Cubic.BoxAsymptotic.HeckeCosineWeights
