import Cubic.Counting.HeightCoefficientData
import Cubic.PoissonSummation.RectangleResidue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian estimates and the earlier pole-removal proof

This file retains the valid proof from the preceding manuscript revision.
The current direct two-residue argument is in `GaussianResidue` and
`GaussianMeanValue`, which reuse the analytic estimates and Fubini theorem here.
The following description concerns the preceding pole-removal argument.

* `hfun` is `h(w) = (w - 1) ζ_E(w) / (w + 2)`, with the pole of `ζ` at `w = 1` removed
  (`zetaOne` fills in `(w - 1) ζ(w)` at `1` via `riemannZeta_residue_one`).
* `rectangle_cauchy`: Cauchy's formula with kernel `e^{(w-s)²}/(w-s)` on the rectangle
  `[1/2, 3] × [t - R, t + R]` (via `ResidueTheoremOnRectangleWithSimplePole`).
* `two_pi_norm_hfun_le`: letting `R → ∞` (the horizontal sides are `O(R⁴ e^{-R²})` by `Growth`),
  `2π |h(s)| ≤ A + (e³/δ) ∫ e^{-(v-t)²} |ζ_E(1/2+iv)| dv`, since `h(3+iv)` is bounded and
  `|h(1/2+iv)| ≤ |ζ_E(1/2+iv)|`.
* `gauss_cauchy_schwarz`, `pointwise`: Cauchy--Schwarz against the Gaussian weight gives
  `|ζ_E(σ+it)|² ≤ K (1 + ∫ e^{-(v-t)²} |ζ_E(1/2+iv)|² dv)`; the integral is of an integrable
  function (`integrable_gauss_zetaE_sq`).
* `mean_value_strip`: integrate over `U ≤ t ≤ 2U`, swap the integrals (Fubini), use the
  critical-line mean value on `[U/2, U]`, `[U, 2U]`, `[2U, 4U]`, and bound the Gaussian tails
  by polynomial growth.

The earlier bound is uniform for every `δ > 0`. The Gaussian
tail is bounded here by `O(U)`, which suffices for `O(U^(1+η))`; the paper gives
the sharper intermediate bound `O(1)`.
-/

noncomputable section

namespace Cubic.Analysis.MeanValueExtension

open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData
open Cubic.PoissonSummation
open Cubic.PoissonSummation.RectangleResidue
open scoped Interval

/-! ### The function `h(w) = (w - 1) ζ_E(w) / (w + 2)` -/

/-- `(w - 1) ζ(w)`, with its removable singularity at `w = 1` filled in. -/
def zetaOne : ℂ → ℂ := Function.update (fun w => (w - 1) * riemannZeta w) 1 1

lemma differentiable_zetaOne : Differentiable ℂ zetaOne := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s ↦ (s - 1) * riemannZeta s)
    (fun s hs ↦ DifferentiableAt.differentiableWithinAt <|
      (differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta (Set.mem_diff_singleton.mp hs).2))
    fun _ hs ↦ Function.update_of_ne (Set.mem_diff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa [zetaOne, continuousWithinAt_update_same] using riemannZeta_residue_one

/-- The preceding manuscript's `h(w) = (w - 1) ζ_E(w) / (w + 2)`, with the pole of `ζ` at `1` removed. -/
def hfun (w : ℂ) : ℂ :=
  zetaOne w * DirichletCharacter.LFunction QuadraticDirichletCharacter.character w / (w + 2)

lemma hfun_eq {w : ℂ} (hw : w ≠ 1) : hfun w = (w - 1) * zetaE w / (w + 2) := by
  simp only [hfun, zetaOne, Function.update_of_ne hw, zetaE]
  ring

lemma differentiableOn_hfun : DifferentiableOn ℂ hfun {w | -2 < w.re} := by
  refine ((differentiable_zetaOne.mul
    QuadraticDirichletCharacter.differentiable_LFunction).differentiableOn).div
    (differentiableOn_id.add_const 2) fun w hw => ?_
  intro h
  have := congrArg Complex.re h
  simp only [add_re, re_ofNat, zero_re] at this
  simp only [mem_setOf_eq] at hw
  linarith

lemma continuousAt_zetaE {w : ℂ} (hw : w ≠ 1) : ContinuousAt zetaE w :=
  ((differentiableAt_riemannZeta hw).mul
    (QuadraticDirichletCharacter.differentiable_LFunction w)).continuousAt

lemma continuous_zetaE_line {c : ℝ} (hc : c ≠ 1) :
    Continuous fun v : ℝ => zetaE ((c : ℂ) + v * I) := by
  rw [continuous_iff_continuousAt]
  intro v
  refine ContinuousAt.comp (g := zetaE) (continuousAt_zetaE ?_) (by fun_prop)
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hc this

/-! ### Real estimates for Gaussians -/

lemma poly_gauss_le {b : ℝ} (hb : 0 < b) (v : ℝ) :
    (1 + |v|) ^ 8 * Real.exp (-b * v ^ 2) ≤
      (Nat.factorial 8 : ℝ) * Real.exp (1 + 1 / (2 * b)) * Real.exp (-(b / 2) * v ^ 2) := by
  have h1 : (1 + |v|) ^ 8 ≤ (Nat.factorial 8 : ℝ) * Real.exp (1 + |v|) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + |v|) (by positivity) 8
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : 1 + |v| + -b * v ^ 2 ≤ 1 + 1 / (2 * b) + -(b / 2) * v ^ 2 := by
    have hsq : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
    have key : 0 ≤ b / 2 * (|v| - 1 / b) ^ 2 := by positivity
    have e : b / 2 * (|v| - 1 / b) ^ 2 = b / 2 * |v| ^ 2 - |v| + 1 / (2 * b) := by
      field_simp
      ring
    rw [hsq]
    nlinarith [sq_nonneg |v|]
  calc (1 + |v|) ^ 8 * Real.exp (-b * v ^ 2)
      ≤ (Nat.factorial 8 : ℝ) * Real.exp (1 + |v|) * Real.exp (-b * v ^ 2) := by
        gcongr
    _ = (Nat.factorial 8 : ℝ) * Real.exp (1 + |v| + -b * v ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ (Nat.factorial 8 : ℝ) * Real.exp (1 + 1 / (2 * b) + -(b / 2) * v ^ 2) := by
        gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]

lemma integrable_poly_gauss {b : ℝ} (hb : 0 < b) :
    Integrable fun v : ℝ => (1 + |v|) ^ 8 * Real.exp (-b * v ^ 2) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul
    ((Nat.factorial 8 : ℝ) * Real.exp (1 + 1 / (2 * b))))
    (by fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact poly_gauss_le hb v

lemma gauss_shift_le (t v : ℝ) :
    Real.exp (-(v - t) ^ 2) ≤ Real.exp (t ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := by
  rw [← Real.exp_add]
  gcongr
  nlinarith [sq_nonneg (v - 2 * t)]

/-- A continuous function of polynomial growth, weighted by a shifted Gaussian, is integrable. -/
lemma integrable_gauss_mul {φ : ℝ → ℝ} (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ v, |φ v| ≤ M * (1 + |v|) ^ 8) (t : ℝ) :
    Integrable fun v => Real.exp (-(v - t) ^ 2) * φ v := by
  refine Integrable.mono' (((integrable_poly_gauss (b := 1 / 2) (by norm_num)).const_mul
    (Real.exp (t ^ 2) * M))) (by fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hM0 : 0 ≤ M * (1 + |v|) ^ 8 := (abs_nonneg _).trans (hM v)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (-(v - t) ^ 2) * |φ v|
      ≤ (Real.exp (t ^ 2) * Real.exp (-(1 / 2) * v ^ 2)) * (M * (1 + |v|) ^ 8) :=
        mul_le_mul (gauss_shift_le t v) (hM v) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma integrable_mul_gauss {φ : ℝ → ℝ} (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ v, |φ v| ≤ M * (1 + |v|) ^ 8) {b : ℝ} (hb : 0 < b) :
    Integrable fun v => φ v * Real.exp (-b * v ^ 2) := by
  refine Integrable.mono' ((integrable_poly_gauss hb).const_mul M)
    (by fun_prop : Continuous _).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  have hM0 : 0 ≤ M * (1 + |v|) ^ 8 := (abs_nonneg _).trans (hM v)
  calc |φ v| * Real.exp (-b * v ^ 2) ≤ M * (1 + |v|) ^ 8 * Real.exp (-b * v ^ 2) := by
        gcongr; exact hM v
    _ = _ := by ring

lemma integral_gauss_shift (t : ℝ) : ∫ v : ℝ, Real.exp (-(v - t) ^ 2) = Real.sqrt Real.pi := by
  have := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at this
  rw [← this]
  exact integral_sub_right_eq_self (fun v => Real.exp (-v ^ 2)) t

lemma integrable_gauss_shift (t : ℝ) : Integrable fun v : ℝ => Real.exp (-(v - t) ^ 2) := by
  have := (integrable_exp_neg_mul_sq (b := 1) one_pos).comp_sub_right t
  simpa only [neg_mul, one_mul] using this

lemma intervalIntegral_le_integral {g : ℝ → ℝ} (hg : Integrable g) (h0 : ∀ v, 0 ≤ g v)
    {a b : ℝ} (hab : a ≤ b) : ∫ v in a..b, g v ≤ ∫ v, g v := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_le_integral hg (Eventually.of_forall h0)


/-! ### Growth hypothesis and elementary bounds on `ζ_E` -/

/-- Polynomial growth of `(s-1) ζ_E(s)` in the strip, supplied separately. -/
def Growth : Prop := ∃ C : ℝ, ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 →
    ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4

lemma Growth.nonneg_const (hG : Growth) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re →
    s.re ≤ 3 → ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4 := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨C, ?_, hC⟩
  have := hC (1 / 2) (by norm_num) (by norm_num)
  have h1 : (1 + |(1 / 2 : ℂ).im|) ^ 4 = 1 := by simp
  rw [h1, mul_one] at this
  exact (norm_nonneg _).trans this

/-- On the critical line, `|ζ_E|` and `|ζ_E|²` have polynomial growth. -/
lemma norm_zetaE_half_le (hG : Growth) : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ,
    ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ≤ M * (1 + |v|) ^ 8 ∧
      ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 ≤ M * (1 + |v|) ^ 8 := by
  obtain ⟨C, hC0, hC⟩ := hG.nonneg_const
  refine ⟨2 * C + 4 * C ^ 2, by positivity, fun v => ?_⟩
  set w : ℂ := (1 / 2 : ℂ) + v * I
  have hre : w.re = 1 / 2 := by simp [w]
  have him : w.im = v := by simp [w]
  have hb := hC w (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [him, norm_mul] at hb
  have hw1 : (1 / 2 : ℝ) ≤ ‖w - 1‖ := by
    have := Complex.abs_re_le_norm (w - 1)
    rw [sub_re, hre, one_re] at this
    norm_num at this
    linarith
  have hz : ‖zetaE w‖ ≤ 2 * C * (1 + |v|) ^ 4 := by
    have hz0 := norm_nonneg (zetaE w)
    nlinarith
  have hv1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have h48 : (1 + |v|) ^ 4 ≤ (1 + |v|) ^ 8 := pow_le_pow_right₀ hv1 (by norm_num)
  have h4 : 0 ≤ (1 + |v|) ^ 4 := by positivity
  constructor
  · calc ‖zetaE w‖ ≤ 2 * C * (1 + |v|) ^ 4 := hz
      _ ≤ 2 * C * (1 + |v|) ^ 8 := by gcongr
      _ ≤ (2 * C + 4 * C ^ 2) * (1 + |v|) ^ 8 := by
          have : 0 ≤ 4 * C ^ 2 * (1 + |v|) ^ 8 := by positivity
          nlinarith
  · calc ‖zetaE w‖ ^ 2 ≤ (2 * C * (1 + |v|) ^ 4) ^ 2 := by gcongr
      _ = 4 * C ^ 2 * (1 + |v|) ^ 8 := by ring
      _ ≤ (2 * C + 4 * C ^ 2) * (1 + |v|) ^ 8 := by
          have : 0 ≤ 2 * C * (1 + |v|) ^ 8 := by positivity
          nlinarith

lemma norm_LSeries_le_of_re_eq_three (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {w : ℂ}
    (hw : w.re = 3) :
    ‖LSeries f w‖ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) 3 n‖ := by
  have hS : Summable fun n : ℕ => ‖LSeries.term (1 : ℕ → ℂ) 3 n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr (by norm_num))
  have hle : ∀ n, ‖LSeries.term f w n‖ ≤ ‖LSeries.term (1 : ℕ → ℂ) 3 n‖ := by
    intro n
    simp only [LSeries.norm_term_eq, hw]
    split
    · rfl
    · have h3 : ((3 : ℂ).re) = 3 := by norm_num
      rw [h3]
      gcongr
      simpa using hf n
  have hS' : Summable fun n => ‖LSeries.term f w n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS
  exact (norm_tsum_le_tsum_norm hS').trans (hS'.tsum_le_tsum hle hS)

/-- `h(3 + iv)` is bounded. -/
lemma norm_hfun_three_le : ∃ B : ℝ, ∀ v : ℝ, ‖hfun ((3 : ℂ) + v * I)‖ ≤ B := by
  set S := ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) 3 n‖
  refine ⟨S * S, fun v => ?_⟩
  set w : ℂ := (3 : ℂ) + v * I
  have hre : w.re = 3 := by simp [w]
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hζ : ‖riemannZeta w‖ ≤ S := by
    rw [← LSeries_one_eq_riemannZeta (by rw [hre]; norm_num)]
    exact norm_LSeries_le_of_re_eq_three _ (fun n => by simp) hre
  have hL : ‖DirichletCharacter.LFunction QuadraticDirichletCharacter.character w‖ ≤ S := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ (by rw [hre]; norm_num)]
    exact norm_LSeries_le_of_re_eq_three _ (fun n => DirichletCharacter.norm_le_one _ _) hre
  have hratio : ‖w - 1‖ ≤ ‖w + 2‖ := by
    have h1 : w - 1 = (2 : ℂ) + v * I := by simp only [w]; ring
    have h2 : w + 2 = (5 : ℂ) + v * I := by simp only [w]; ring
    rw [h1, h2]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    nlinarith
  have hpos : 0 < ‖w + 2‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h; simp [w] at this; norm_num at this
  rw [hfun_eq hw1, zetaE, norm_div, norm_mul, norm_mul, div_le_iff₀ hpos]
  calc ‖w - 1‖ * (‖riemannZeta w‖ *
        ‖DirichletCharacter.LFunction QuadraticDirichletCharacter.character w‖)
      ≤ ‖w + 2‖ * (S * S) := by gcongr
    _ = S * S * ‖w + 2‖ := by ring


/-! ### Cauchy's formula with the Gaussian kernel on a rectangle -/

/-- The integrand `h(w) e^{(w-s)²} / (w - s)` of Cauchy's formula. -/
def kernelIntegrand (s w : ℂ) : ℂ := hfun w * Complex.exp ((w - s) ^ 2) / (w - s)

/-- Cauchy's formula for `h` with kernel `e^{(w-s)²} / (w-s)` on the rectangle
`[1/2, 3] × [Im s - R, Im s + R]`. -/
lemma rectangle_cauchy {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 3) {R : ℝ} (hR : 0 < R) :
    RectangleIntegral (kernelIntegrand s)
      ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I) ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I) =
      2 * Real.pi * I * hfun s := by
  set z : ℂ := (1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I
  set z' : ℂ := (3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hzim : z.im = s.im - R := by simp [z]
  have hz're : z'.re = 3 := by simp [z']
  have hz'im : z'.im = s.im + R := by simp [z']
  set F : ℂ → ℂ := fun w => hfun w * Complex.exp ((w - s) ^ 2)
  have hS : IsOpen {w : ℂ | -2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsS : {w : ℂ | -2 < w.re} ∈ 𝓝 s := hS.mem_nhds (by show -2 < s.re; linarith)
  have hF : DifferentiableOn ℂ F {w | -2 < w.re} :=
    differentiableOn_hfun.mul (by fun_prop)
  have hg : DifferentiableOn ℂ (dslope F s) {w | -2 < w.re} :=
    (Complex.differentiableOn_dslope hsS).mpr hF
  have hrect : Rectangle z z' ⊆ {w | -2 < w.re} := by
    intro w hw
    have h1 : w.re ∈ [[z.re, z'.re]] := hw.1
    rw [hzre, hz're, uIcc_of_le (by norm_num)] at h1
    show -2 < w.re
    linarith [h1.1]
  have hmem : Rectangle z z' ∈ 𝓝 s := by
    rw [rectangle_mem_nhds_iff, hzre, hz're, hzim, hz'im, uIoo_of_le (by norm_num),
      uIoo_of_le (by linarith)]
    exact ⟨⟨hs1, hs2⟩, ⟨by linarith, by linarith⟩⟩
  have key := ResidueTheoremOnRectangleWithSimplePole (f := kernelIntegrand s)
    (g := dslope F s) (A := hfun s)
    (by rw [hzre, hz're]; norm_num) (by rw [hzim, hz'im]; linarith) hmem (hg.mono hrect) ?_
  · rw [RectangleIntegral', smul_eq_mul] at key
    rw [← key]
    have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp
  · intro w hw
    have hws : w - s ≠ 0 := sub_ne_zero.mpr hw.2
    simp only [Pi.sub_apply, kernelIntegrand]
    rw [dslope_of_ne _ hw.2, slope_def_field]
    simp only [F, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Complex.exp_zero, mul_one]
    field_simp


/-! ### Bounds for the kernel integrand on the sides of the rectangle -/

lemma norm_kernelIntegrand (s w : ℂ) :
    ‖kernelIntegrand s w‖ =
      ‖hfun w‖ * Real.exp ((w.re - s.re) ^ 2 - (w.im - s.im) ^ 2) / ‖w - s‖ := by
  rw [kernelIntegrand, norm_div, norm_mul, Complex.norm_exp]
  congr 3
  simp [pow_two, mul_re]

lemma norm_hfun_le_norm_zetaE_of_re {w : ℂ} (hw : w.re = 1 / 2) : ‖hfun w‖ ≤ ‖zetaE w‖ := by
  have hw1 : w ≠ 1 := by
    intro h; rw [h] at hw; norm_num at hw
  have hpos : 0 < ‖w + 2‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h; simp [hw] at this
    norm_num at this
  have hratio : ‖w - 1‖ ≤ ‖w + 2‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, hw]
    nlinarith
  rw [hfun_eq hw1, norm_div, norm_mul, div_le_iff₀ hpos]
  calc ‖w - 1‖ * ‖zetaE w‖ ≤ ‖w + 2‖ * ‖zetaE w‖ := by gcongr
    _ = ‖zetaE w‖ * ‖w + 2‖ := by ring

/-- The right side `Re w = 3`. -/
lemma norm_kernel_right_le {B : ℝ} (hB : ∀ v : ℝ, ‖hfun ((3 : ℂ) + v * I)‖ ≤ B) {s : ℂ}
    (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) (v : ℝ) :
    ‖kernelIntegrand s ((3 : ℂ) + v * I)‖ ≤ B * Real.exp 7 * Real.exp (-(v - s.im) ^ 2) := by
  set w : ℂ := (3 : ℂ) + v * I
  have hre : w.re = 3 := by simp [w]
  have him : w.im = v := by simp [w]
  have hdist : 1 ≤ ‖w - s‖ := by
    have := Complex.abs_re_le_norm (w - s)
    rw [sub_re, hre] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [norm_kernelIntegrand, hre, him, div_le_iff₀ (by linarith)]
  have hexp : Real.exp ((3 - s.re) ^ 2 - (v - s.im) ^ 2) ≤
      Real.exp 7 * Real.exp (-(v - s.im) ^ 2) := by
    rw [← Real.exp_add]
    gcongr
    nlinarith
  calc ‖hfun w‖ * Real.exp ((3 - s.re) ^ 2 - (v - s.im) ^ 2)
      ≤ B * (Real.exp 7 * Real.exp (-(v - s.im) ^ 2)) := by
        gcongr
        exact hB v
    _ ≤ B * Real.exp 7 * Real.exp (-(v - s.im) ^ 2) * ‖w - s‖ := by
        rw [← mul_assoc]
        have : 0 ≤ B * Real.exp 7 * Real.exp (-(v - s.im) ^ 2) := by positivity
        nlinarith

/-- The left side `Re w = 1/2`. -/
lemma norm_kernel_left_le {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs1 : 1 / 2 + δ ≤ s.re)
    (hs2 : s.re ≤ 2) (v : ℝ) :
    ‖kernelIntegrand s ((1 / 2 : ℂ) + v * I)‖ ≤
      Real.exp 3 / δ * (Real.exp (-(v - s.im) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖) := by
  set w : ℂ := (1 / 2 : ℂ) + v * I
  have hre : w.re = 1 / 2 := by simp [w]
  have him : w.im = v := by simp [w]
  have hdist : δ ≤ ‖w - s‖ := by
    have := Complex.abs_re_le_norm (w - s)
    rw [sub_re, hre] at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  have hexp : Real.exp ((1 / 2 - s.re) ^ 2 - (v - s.im) ^ 2) ≤
      Real.exp 3 * Real.exp (-(v - s.im) ^ 2) := by
    rw [← Real.exp_add]
    gcongr
    nlinarith
  rw [norm_kernelIntegrand, hre, him, div_le_iff₀ (by linarith)]
  calc ‖hfun w‖ * Real.exp ((1 / 2 - s.re) ^ 2 - (v - s.im) ^ 2)
      ≤ ‖zetaE w‖ * (Real.exp 3 * Real.exp (-(v - s.im) ^ 2)) := by
        gcongr
        exact norm_hfun_le_norm_zetaE_of_re hre
    _ = Real.exp 3 / δ * (Real.exp (-(v - s.im) ^ 2) * ‖zetaE w‖) * δ := by
        field_simp
    _ ≤ Real.exp 3 / δ * (Real.exp (-(v - s.im) ^ 2) * ‖zetaE w‖) * ‖w - s‖ := by
        gcongr

/-- The horizontal sides `Im w = y` with `|y - Im s| = R ≥ 1` and `y ≠ 0`. -/
lemma norm_kernel_horizontal_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 → ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4)
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) {R y : ℝ} (hR : 1 ≤ R)
    (hy : |y - s.im| = R) (hy0 : y ≠ 0) {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 3) :
    ‖kernelIntegrand s ((u : ℂ) + y * I)‖ ≤
      C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) := by
  set w : ℂ := (u : ℂ) + y * I
  have hre : w.re = u := by simp [w]
  have him : w.im = y := by simp [w]
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [him] at this; simp at this; exact hy0 this
  have hdist : R ≤ ‖w - s‖ := by
    have := Complex.abs_im_le_norm (w - s)
    rw [sub_im, him, hy] at this
    exact this
  have hw2 : 1 ≤ ‖w + 2‖ := by
    have := Complex.abs_re_le_norm (w + 2)
    rw [add_re, hre] at this
    simp only [re_ofNat] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hyle : |y| ≤ |s.im| + R := by
    have := abs_sub_abs_le_abs_sub y s.im
    linarith
  have hh : ‖hfun w‖ ≤ C * (1 + |s.im| + R) ^ 4 := by
    rw [hfun_eq hw1, norm_div, div_le_iff₀ (by linarith)]
    have h1 := hC w (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at h1
    calc ‖(w - 1) * zetaE w‖ ≤ C * (1 + |y|) ^ 4 := h1
      _ ≤ C * (1 + |s.im| + R) ^ 4 := by gcongr C * ?_ ^ 4; linarith
      _ ≤ C * (1 + |s.im| + R) ^ 4 * ‖w + 2‖ := by
          have : 0 ≤ C * (1 + |s.im| + R) ^ 4 := by
            have : 0 ≤ 1 + |s.im| + R := by positivity
            positivity
          nlinarith
  have hexp : Real.exp ((u - s.re) ^ 2 - (y - s.im) ^ 2) ≤
      Real.exp 7 * Real.exp (-R ^ 2) := by
    rw [← Real.exp_add]
    gcongr
    have : (y - s.im) ^ 2 = R ^ 2 := by rw [← hy, sq_abs]
    rw [this]
    nlinarith
  rw [norm_kernelIntegrand, hre, him, div_le_iff₀ (by linarith)]
  have hK0 : 0 ≤ C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) := by
    have : 0 ≤ 1 + |s.im| + R := by positivity
    positivity
  calc ‖hfun w‖ * Real.exp ((u - s.re) ^ 2 - (y - s.im) ^ 2)
      ≤ C * (1 + |s.im| + R) ^ 4 * (Real.exp 7 * Real.exp (-R ^ 2)) := by
        gcongr
    _ = C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) * 1 := by ring
    _ ≤ _ := by gcongr; linarith


/-- `rectangle_cauchy` with the four sides written out. -/
lemma rectangle_cauchy' {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 3) {R : ℝ} (hR : 0 < R) :
    (∫ x in (1 / 2 : ℝ)..3, kernelIntegrand s ((x : ℂ) + ((s.im - R : ℝ) : ℂ) * I)) -
      (∫ x in (1 / 2 : ℝ)..3, kernelIntegrand s ((x : ℂ) + ((s.im + R : ℝ) : ℂ) * I)) +
      I * (∫ y in (s.im - R)..(s.im + R), kernelIntegrand s ((3 : ℂ) + y * I)) -
      I * (∫ y in (s.im - R)..(s.im + R), kernelIntegrand s ((1 / 2 : ℂ) + y * I)) =
      2 * Real.pi * I * hfun s := by
  have key := rectangle_cauchy hs1 hs2 hR
  have e1 : ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I).re = 1 / 2 := by simp
  have e2 : ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I).im = s.im - R := by simp
  have e3 : ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I).re = 3 := by simp
  have e4 : ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I).im = s.im + R := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, e1, e2, e3, e4, smul_eq_mul] at key
  have c3 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  have c12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  rw [c3, c12] at key
  exact key

lemma continuous_zetaE_half : Continuous fun v : ℝ => zetaE ((1 / 2 : ℂ) + v * I) := by
  have := continuous_zetaE_line (c := 1 / 2) (by norm_num)
  have c12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  simpa only [c12] using this

lemma integrable_gauss_zetaE (hG : Growth) (t : ℝ) :
    Integrable fun v : ℝ => Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ := by
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  exact integrable_gauss_mul continuous_zetaE_half.norm
    (fun v => by rw [abs_of_nonneg (norm_nonneg _)]; exact (hM v).1) t

lemma integrable_gauss_zetaE_sq (hG : Growth) (t : ℝ) :
    Integrable fun v : ℝ => Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 := by
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  exact integrable_gauss_mul (continuous_zetaE_half.norm.pow 2)
    (fun v => by rw [abs_of_nonneg (by positivity)]; exact (hM v).2) t

/-- The horizontal contributions tend to zero as the rectangle grows. -/
lemma tendsto_horizontal_error {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) :
    Tendsto (fun R : ℝ => C * (1 + a + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)) atTop (𝓝 0) := by
  have hup : Tendsto (fun R : ℝ => C * 16 * Real.exp 7 * (R ^ 4 * Real.exp (-R))) atTop
      (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul
      (C * 16 * Real.exp 7)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with R hR
    have : 0 ≤ 1 + a + R := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (1 + a)] with R hR
    have hR1 : 1 ≤ R := by linarith
    have h1 : (1 + a + R) ^ 4 ≤ 16 * R ^ 4 := by
      have : 1 + a + R ≤ 2 * R := by linarith
      calc (1 + a + R) ^ 4 ≤ (2 * R) ^ 4 := by gcongr
        _ = 16 * R ^ 4 := by ring
    have h2 : Real.exp (-R ^ 2) ≤ Real.exp (-R) := by
      gcongr
      nlinarith
    calc C * (1 + a + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)
        ≤ C * (16 * R ^ 4) * Real.exp 7 * Real.exp (-R) := by gcongr
      _ = C * 16 * Real.exp 7 * (R ^ 4 * Real.exp (-R)) := by ring

lemma norm_four_le (a b c d : ℂ) : ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have := norm_sub_le (a - b + c) d
  have := norm_add_le (a - b) c
  have := norm_sub_le a b
  linarith

/-- Cauchy's formula, after letting the rectangle grow:
`2π |h(s)| ≤ A + (e³/δ) ∫ e^{-(v-t)²} |ζ_E(1/2+iv)| dv`. -/
lemma two_pi_norm_hfun_le (hG : Growth) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 →
      2 * Real.pi * ‖hfun s‖ ≤ A + Real.exp 3 / δ *
        ∫ v : ℝ, Real.exp (-(v - s.im) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := hG.nonneg_const
  obtain ⟨B, hB⟩ := norm_hfun_three_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B * Real.exp 7 * Real.sqrt Real.pi, by positivity, fun s hs1 hs2 => ?_⟩
  set t := s.im with ht
  set J := ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
  set err : ℝ → ℝ := fun R => C * (1 + |t| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)
  have hbound : ∀ R : ℝ, |t| + 1 ≤ R →
      2 * Real.pi * ‖hfun s‖ ≤ 5 / 2 * err R + 5 / 2 * err R +
        B * Real.exp 7 * Real.sqrt Real.pi + Real.exp 3 / δ * J := by
    intro R hR
    have hR1 : 1 ≤ R := by linarith [abs_nonneg t]
    have hR0 : 0 < R := by linarith
    have key := rectangle_cauchy' (s := s) (by linarith) (by linarith) hR0
    have hlhs : ‖2 * (Real.pi : ℂ) * I * hfun s‖ = 2 * Real.pi * ‖hfun s‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    -- horizontal sides
    have hH : ∀ y : ℝ, |y - t| = R → y ≠ 0 →
        ‖∫ x in (1 / 2 : ℝ)..3, kernelIntegrand s ((x : ℂ) + (y : ℂ) * I)‖ ≤ 5 / 2 * err R := by
      intro y hy hy0
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (1 / 2 : ℝ)) (b := 3) (C := err R)
        (f := fun x : ℝ => kernelIntegrand s ((x : ℂ) + (y : ℂ) * I)) (fun x hx => by
          rw [uIoc_of_le (by norm_num)] at hx
          exact norm_kernel_horizontal_le hC0 hC (by linarith) hs2 hR1 hy hy0
            (by linarith [hx.1]) hx.2)
      rw [show |(3 : ℝ) - 1 / 2| = 5 / 2 by norm_num] at this
      linarith
    have hH1 := hH (t - R) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hR0])
      (by intro h; have := le_abs_self t; linarith)
    have hH2 := hH (t + R) (by rw [add_sub_cancel_left, abs_of_pos hR0])
      (by intro h; have := neg_abs_le t; linarith)
    -- right side
    have hV3 : ‖∫ y in (t - R)..(t + R), kernelIntegrand s ((3 : ℂ) + y * I)‖ ≤
        B * Real.exp 7 * Real.sqrt Real.pi := by
      have hg : Integrable fun y : ℝ => B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
        (integrable_gauss_shift t).const_mul _
      calc _ ≤ ∫ y in (t - R)..(t + R), B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
            intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun y _ => norm_kernel_right_le hB (by linarith) hs2 y)
              hg.intervalIntegrable
        _ ≤ ∫ y, B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
            intervalIntegral_le_integral hg (fun y => by positivity) (by linarith)
        _ = B * Real.exp 7 * Real.sqrt Real.pi := by
            rw [integral_const_mul, integral_gauss_shift]
    -- left side
    have hVh : ‖∫ y in (t - R)..(t + R), kernelIntegrand s ((1 / 2 : ℂ) + y * I)‖ ≤
        Real.exp 3 / δ * J := by
      have hg : Integrable fun y : ℝ => Real.exp 3 / δ *
          (Real.exp (-(y - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
        (integrable_gauss_zetaE hG t).const_mul _
      calc _ ≤ ∫ y in (t - R)..(t + R), Real.exp 3 / δ *
              (Real.exp (-(y - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
            intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun y _ => norm_kernel_left_le hδ hs1 hs2 y)
              hg.intervalIntegrable
        _ ≤ ∫ y, Real.exp 3 / δ *
              (Real.exp (-(y - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
            intervalIntegral_le_integral hg (fun y => by positivity) (by linarith)
        _ = Real.exp 3 / δ * J := by rw [integral_const_mul]
    rw [← hlhs, ← key]
    refine (norm_four_le _ _ _ _).trans ?_
    rw [norm_mul, norm_mul, norm_I, one_mul, one_mul]
    linarith
  have hlim : Tendsto (fun R => 5 / 2 * err R + 5 / 2 * err R +
      B * Real.exp 7 * Real.sqrt Real.pi + Real.exp 3 / δ * J) atTop
      (𝓝 (5 / 2 * 0 + 5 / 2 * 0 + B * Real.exp 7 * Real.sqrt Real.pi + Real.exp 3 / δ * J)) := by
    have h := tendsto_horizontal_error hC0 (abs_nonneg t)
    exact ((((h.const_mul _).add (h.const_mul _)).add_const _).add_const _)
  have := ge_of_tendsto hlim ((eventually_ge_atTop (|t| + 1)).mono hbound)
  simpa using this


/-! ### The pointwise bound -/

/-- Cauchy--Schwarz against the Gaussian weight, in the form
`∫ e^{-(v-t)²} |ζ_E| ≤ λ (√π + 1) / 2` with `λ = (1 + ∫ e^{-(v-t)²} |ζ_E|²)^{1/2}`. -/
lemma gauss_cauchy_schwarz (hG : Growth) (t : ℝ) :
    ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ≤
      Real.sqrt (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) *
        (Real.sqrt Real.pi + 1) / 2 := by
  set I₂ := ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun v => by positivity
  set l := Real.sqrt (1 + I₂)
  have hl : 0 < l := Real.sqrt_pos.mpr (by linarith)
  have hl2 : l ^ 2 = 1 + I₂ := Real.sq_sqrt (by linarith)
  have hint : Integrable fun v : ℝ => (l * Real.exp (-(v - t) ^ 2) +
      Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 / l) / 2 :=
    ((((integrable_gauss_shift t).const_mul l).add
      ((integrable_gauss_zetaE_sq hG t).div_const l)).div_const 2)
  calc ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
      ≤ ∫ v : ℝ, (l * Real.exp (-(v - t) ^ 2) +
          Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 / l) / 2 := by
        refine integral_mono (integrable_gauss_zetaE hG t) hint fun v => ?_
        set e := Real.exp (-(v - t) ^ 2)
        set y := ‖zetaE ((1 / 2 : ℂ) + v * I)‖
        have he : 0 ≤ e := (Real.exp_pos _).le
        have eq : (l * e + e * y ^ 2 / l) / 2 - e * y = e * (l - y) ^ 2 / (2 * l) := by
          field_simp
          ring
        have : 0 ≤ e * (l - y) ^ 2 / (2 * l) := by positivity
        linarith
    _ = (l * Real.sqrt Real.pi + I₂ / l) / 2 := by
        rw [integral_div, integral_add ((integrable_gauss_shift t).const_mul l)
          ((integrable_gauss_zetaE_sq hG t).div_const l), integral_const_mul, integral_div,
          integral_gauss_shift]
    _ ≤ l * (Real.sqrt Real.pi + 1) / 2 := by
        have : I₂ / l ≤ l := by
          rw [div_le_iff₀ hl]
          nlinarith
        linarith

/-- The pointwise bound, with a nonnegative constant. -/
theorem pointwise_nonneg (hG : Growth) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ t : ℝ, 2 ≤ t →
      ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤
        K * (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * Complex.I)‖ ^ 2) := by
  obtain ⟨A, hA0, hA⟩ := two_pi_norm_hfun_le hG hδ
  have hp : 0 < 2 * Real.pi := by positivity
  set a := 5 / 2 * A / (2 * Real.pi)
  set b := 5 / 2 * (Real.exp 3 / δ * ((Real.sqrt Real.pi + 1) / 2)) / (2 * Real.pi)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  refine ⟨2 * a ^ 2 + 2 * b ^ 2, by positivity, fun σ hσ1 hσ2 t ht => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  set I₂ := ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2
  set J := ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun v => by positivity
  set l := Real.sqrt (1 + I₂)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hl2 : l ^ 2 = 1 + I₂ := Real.sq_sqrt (by linarith)
  have hJ : J ≤ l * (Real.sqrt Real.pi + 1) / 2 := gauss_cauchy_schwarz hG t
  -- `2π |h(s)| ≤ A + (e³/δ) J`
  have hh := hA s (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
  rw [him] at hh
  -- `|ζ_E(s)| ≤ (5/2) |h(s)|`
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [him] at this; simp at this; linarith
  have hsub : t ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [sub_im, him, one_im, sub_zero, abs_of_pos (by linarith)] at this
    exact this
  have hadd : ‖s + 2‖ ≤ ‖s - 1‖ + 3 := by
    have := norm_add_le (s - 1) 3
    rw [show s - 1 + 3 = s + 2 by ring] at this
    simpa using this
  have hζ : ‖zetaE s‖ ≤ 5 / 2 * ‖hfun s‖ := by
    have hpos : 0 < ‖s - 1‖ := by linarith
    have heq : zetaE s = hfun s * (s + 2) / (s - 1) := by
      rw [hfun_eq hs1]
      have h2 : s + 2 ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [add_re, hre] at this; simp at this
        linarith
      have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp
    rw [heq, norm_div, norm_mul, div_le_iff₀ hpos]
    have := norm_nonneg (hfun s)
    nlinarith
  have hζ' : ‖zetaE s‖ ≤ a + b * l := by
    have h1 : ‖hfun s‖ ≤ (A + Real.exp 3 / δ * J) / (2 * Real.pi) := by
      rw [le_div_iff₀ hp]; linarith
    have h2 : A + Real.exp 3 / δ * J ≤
        A + Real.exp 3 / δ * (l * (Real.sqrt Real.pi + 1) / 2) := by gcongr
    calc ‖zetaE s‖ ≤ 5 / 2 * ((A + Real.exp 3 / δ * (l * (Real.sqrt Real.pi + 1) / 2)) /
          (2 * Real.pi)) := by
          refine hζ.trans ?_
          gcongr
          exact h1.trans (by gcongr)
      _ = a + b * l := by simp only [a, b]; field_simp
  calc ‖zetaE s‖ ^ 2 ≤ (a + b * l) ^ 2 := by gcongr
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 * l ^ 2 := by nlinarith [sq_nonneg (a - b * l)]
    _ = 2 * a ^ 2 + 2 * b ^ 2 * (1 + I₂) := by rw [hl2]
    _ ≤ (2 * a ^ 2 + 2 * b ^ 2) * (1 + I₂) := by nlinarith [sq_nonneg a]

/-- The paper's pointwise bound, for `β ≤ σ ≤ 2` and `t ≥ 2`. -/
theorem pointwise (hG : Growth) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ t : ℝ, 2 ≤ t →
      ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤
        K * (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * Complex.I)‖ ^ 2) := by
  obtain ⟨K, -, hK⟩ := pointwise_nonneg hG δ hδ
  exact ⟨K, hK⟩


/-! ### Integrating the pointwise bound over `U ≤ t ≤ 2U` -/

/-- The critical-line mean value on `[a, 2a]` for every `a ≥ 1`; below `a = 2` the
integrand is bounded by polynomial growth. -/
lemma mean_value_from_one (hMV : MeanValue) (hG : Growth) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, 1 ≤ a →
      ∫ v in a..2 * a, ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 ≤ K * a ^ (1 + η) := by
  obtain ⟨K, hK⟩ := hMV η hη
  obtain ⟨M, hM0, hM⟩ := norm_zetaE_half_le hG
  refine ⟨max K 0 + M * 5 ^ 8, by positivity, fun a ha => ?_⟩
  have hpow : 0 ≤ a ^ (1 + η) := by positivity
  have hapow : a ≤ a ^ (1 + η) := by
    calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le ha (by linarith)
  by_cases h2 : 2 ≤ a
  · calc _ ≤ K * a ^ (1 + η) := hK a h2
      _ ≤ (max K 0 + M * 5 ^ 8) * a ^ (1 + η) := by
          gcongr
          have : 0 ≤ M * 5 ^ 8 := by positivity
          linarith [le_max_left K 0]
  · push_neg at h2
    have hc : Continuous fun v : ℝ => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 :=
      continuous_zetaE_half.norm.pow 2
    calc _ ≤ ∫ v in a..2 * a, M * 5 ^ 8 := by
          refine intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
            intervalIntegrable_const fun v hv => ?_
          have hv0 : 0 ≤ v := by linarith [hv.1]
          have h8 : (1 + |v|) ^ 8 ≤ 5 ^ 8 := by
            rw [abs_of_nonneg hv0]
            gcongr
            linarith [hv.2]
          calc _ ≤ M * (1 + |v|) ^ 8 := (hM v).2
            _ ≤ M * 5 ^ 8 := by gcongr
      _ = a * (M * 5 ^ 8) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ a ^ (1 + η) * (M * 5 ^ 8) := by gcongr
      _ ≤ (max K 0 + M * 5 ^ 8) * a ^ (1 + η) := by
          rw [mul_comm]
          gcongr
          linarith [le_max_right K 0]

/-- The Gaussian window `∫_U^{2U} e^{-(v-t)²} dt` is at most `√π` near `[U, 2U]`, and far
from it is at most `U e^{-v²/4}`. -/
lemma gauss_window_le {U : ℝ} (hU : 2 ≤ U) (f : ℝ → ℝ) (v : ℝ) (hz : 0 ≤ f v) :
    f v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤
      Real.sqrt Real.pi * (Icc (U / 2) (4 * U)).indicator f v +
        U * (f v * Real.exp (-(1 / 4) * v ^ 2)) := by
  set z := f v
  have hsym : ∀ t : ℝ, (v - t) ^ 2 = (t - v) ^ 2 := fun t => by ring
  by_cases hv : v ∈ Icc (U / 2) (4 * U)
  · rw [indicator_of_mem hv]
    have hW : ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤ Real.sqrt Real.pi := by
      simp_rw [hsym]
      rw [← integral_gauss_shift v]
      exact intervalIntegral_le_integral (integrable_gauss_shift v)
        (fun t => (Real.exp_pos _).le) (by linarith)
    have : 0 ≤ U * (z * Real.exp (-(1 / 4) * v ^ 2)) := by
      have : 0 ≤ U := by linarith
      positivity
    nlinarith
  · rw [indicator_of_notMem hv, mul_zero, zero_add]
    have hfar : ∀ t ∈ Icc U (2 * U), Real.exp (-(v - t) ^ 2) ≤ Real.exp (-(1 / 4) * v ^ 2) := by
      intro t ht
      gcongr
      have hmain : |v| / 2 ≤ |t - v| := by
        simp only [mem_Icc, not_and_or, not_le] at hv
        rcases hv with hv | hv
        · have h1 : 0 ≤ t - v := by linarith [ht.1]
          rw [abs_of_nonneg h1]
          rcases le_or_gt 0 v with h0 | h0
          · rw [abs_of_nonneg h0]; linarith [ht.1]
          · rw [abs_of_neg h0]; linarith [ht.1]
        · have h1 : t - v < 0 := by linarith [ht.2]
          rw [abs_of_neg h1, abs_of_pos (by linarith)]
          linarith [ht.2]
      have h0 : 0 ≤ |v| / 2 := by positivity
      have := pow_le_pow_left₀ h0 hmain 2
      rw [div_pow, sq_abs, sq_abs] at this
      nlinarith
    have hW : ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤ U * Real.exp (-(1 / 4) * v ^ 2) := by
      calc _ ≤ ∫ t in U..2 * U, Real.exp (-(1 / 4) * v ^ 2) :=
            intervalIntegral.integral_mono_on (by linarith)
              ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(v - t) ^ 2)).intervalIntegrable _ _)
              intervalIntegrable_const hfar
        _ = U * Real.exp (-(1 / 4) * v ^ 2) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
    calc f v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2)
        ≤ z * (U * Real.exp (-(1 / 4) * v ^ 2)) := by gcongr
      _ = U * (z * Real.exp (-(1 / 4) * v ^ 2)) := by ring


/-- Fubini for the Gaussian average of `|ζ_E(1/2+iv)|²` over `U ≤ t ≤ 2U`. -/
lemma gauss_average_swap (hG : Growth) {U : ℝ} (hU : 2 ≤ U) :
    IntervalIntegrable (fun t : ℝ => ∫ v : ℝ, Real.exp (-(v - t) ^ 2) *
        ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) volume U (2 * U) ∧
      Integrable (fun v : ℝ => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 *
        ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2)) ∧
      ∫ t in U..2 * U, (∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2) =
        ∫ v : ℝ, ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 *
          ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) := by
  set Z : ℝ → ℝ := fun v => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 with hZdef
  have hZc : Continuous Z := continuous_zetaE_half.norm.pow 2
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  have hZM : ∀ v, |Z v| ≤ M * (1 + |v|) ^ 8 := fun v => by
    rw [abs_of_nonneg (by positivity)]; exact (hM v).2
  have hUU : U ≤ 2 * U := by linarith
  set μ : Measure ℝ := volume.restrict (Ioc U (2 * U))
  set f : ℝ → ℝ → ℝ := fun t v => Real.exp (-(v - t) ^ 2) * Z v
  have hint : Integrable (Function.uncurry f) (μ.prod volume) := by
    have hf : Integrable (fun t : ℝ => Real.exp (t ^ 2)) μ :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (t ^ 2)).integrableOn_Icc
        (a := U) (b := 2 * U)).mono_set Ioc_subset_Icc_self
    have hg := integrable_mul_gauss hZc hZM (b := 1 / 2) (by norm_num)
    refine Integrable.mono' (hf.mul_prod hg) ?_ (Eventually.of_forall fun p => ?_)
    · exact (Continuous.mul (by fun_prop) (hZc.comp continuous_snd)).aestronglyMeasurable
    · simp only [Function.uncurry, f]
      have hZ0 : 0 ≤ Z p.2 := by positivity
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hZ0]
      have := gauss_shift_le p.1 p.2
      calc Real.exp (-(p.2 - p.1) ^ 2) * Z p.2
          ≤ Real.exp (p.1 ^ 2) * Real.exp (-(1 / 2) * p.2 ^ 2) * Z p.2 := by gcongr
        _ = _ := by ring
  have hswap := integral_integral_swap hint
  have hinner : ∀ v : ℝ, ∫ t, f t v ∂μ = Z v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) := by
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

theorem mean_value_strip (hMV : MeanValue) (hG : Growth) (δ : ℝ) (hδ : 0 < δ)
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤ K * U ^ (1 + η) := by
  obtain ⟨K₀, hK₀, hpt⟩ := pointwise_nonneg hG δ hδ
  obtain ⟨K', hK', hmv⟩ := mean_value_from_one hMV hG hη
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  set Z : ℝ → ℝ := fun v => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 with hZdef
  have hZc : Continuous Z := continuous_zetaE_half.norm.pow 2
  have hZ0 : ∀ v, 0 ≤ Z v := fun v => by positivity
  have hZM : ∀ v, |Z v| ≤ M * (1 + |v|) ^ 8 := fun v => by
    rw [abs_of_nonneg (hZ0 v)]; exact (hM v).2
  have hgauss := integrable_mul_gauss hZc hZM (b := 1 / 4) (by norm_num)
  set Mint := ∫ v : ℝ, Z v * Real.exp (-(1 / 4) * v ^ 2)
  have hMint : 0 ≤ Mint := integral_nonneg fun v => mul_nonneg (hZ0 v) (Real.exp_pos _).le
  set p := 1 + η
  refine ⟨K₀ * (1 + Real.sqrt Real.pi * (K' * (2 + 2 ^ p)) + Mint),
    fun σ hσ1 hσ2 U hU => ?_⟩
  obtain ⟨hI₂int, hZWint, hswap⟩ := gauss_average_swap hG hU
  have hU0 : 0 ≤ U := by linarith
  have hUp0 : 0 ≤ U ^ p := by positivity
  have hUp : U ≤ U ^ p := by
    calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ p := Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp only [p]; linarith)
  -- the critical-line mean value on `[U/2, 4U]`
  have hnear : ∫ v in U / 2..4 * U, Z v ≤ K' * (2 + 2 ^ p) * U ^ p := by
    have hi : ∀ a b : ℝ, IntervalIntegrable Z volume a b := fun a b => hZc.intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ (2 * U)) (hi _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (hi _ U) (hi _ _)]
    have h1 := hmv (U / 2) (by linarith)
    have h2 := hmv U (by linarith)
    have h3 := hmv (2 * U) (by linarith)
    rw [show 2 * (U / 2) = U by ring] at h1
    rw [show 2 * (2 * U) = 4 * U by ring] at h3
    have e1 : (U / 2) ^ p ≤ U ^ p := Real.rpow_le_rpow (by positivity) (by linarith)
      (by simp only [p]; linarith)
    have e3 : (2 * U) ^ p = 2 ^ p * U ^ p := Real.mul_rpow (by norm_num) hU0
    rw [e3] at h3
    have : K' * (U / 2) ^ p ≤ K' * U ^ p := by gcongr
    nlinarith
  -- the Gaussian average of `|ζ_E(1/2+iv)|²`
  have hI₂ : ∫ t in U..2 * U, (∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v) ≤
      Real.sqrt Real.pi * (K' * (2 + 2 ^ p) * U ^ p) + U * Mint := by
    have hind : Integrable ((Icc (U / 2) (4 * U)).indicator Z) :=
      (hZc.integrableOn_Icc).integrable_indicator measurableSet_Icc
    rw [hswap]
    calc ∫ v : ℝ, Z v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2)
        ≤ ∫ v : ℝ, (Real.sqrt Real.pi * (Icc (U / 2) (4 * U)).indicator Z v +
            U * (Z v * Real.exp (-(1 / 4) * v ^ 2))) :=
          integral_mono hZWint ((hind.const_mul _).add (hgauss.const_mul _))
            fun v => gauss_window_le hU Z v (hZ0 v)
      _ = Real.sqrt Real.pi * (∫ v in U / 2..4 * U, Z v) + U * Mint := by
          rw [integral_add (hind.const_mul _) (hgauss.const_mul _), integral_const_mul,
            integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by linarith)]
      _ ≤ _ := by gcongr
  -- integrate the pointwise bound
  have hLint : IntervalIntegrable (fun t : ℝ => ‖zetaE (σ + t * Complex.I)‖ ^ 2) volume U
      (2 * U) := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [uIcc_of_le (by linarith)] at ht
    have hne : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [ht.1]
    exact ((continuousAt_zetaE hne).comp (f := fun t : ℝ => (σ : ℂ) + t * I)
      (by fun_prop)).norm.pow 2
  calc ∫ t in U..2 * U, ‖zetaE (σ + t * Complex.I)‖ ^ 2
      ≤ ∫ t in U..2 * U, K₀ * (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v) :=
        intervalIntegral.integral_mono_on (by linarith) hLint
          ((IntervalIntegrable.add intervalIntegrable_const hI₂int).const_mul K₀)
          fun t ht => hpt σ hσ1 hσ2 t (by linarith [ht.1])
    _ = K₀ * (U + ∫ t in U..2 * U, (∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add intervalIntegrable_const hI₂int,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ K₀ * (U + (Real.sqrt Real.pi * (K' * (2 + 2 ^ p) * U ^ p) + U * Mint)) := by
        gcongr
    _ ≤ K₀ * ((1 + Real.sqrt Real.pi * (K' * (2 + 2 ^ p)) + Mint) * U ^ p) := by
        gcongr
        have := mul_le_mul_of_nonneg_left hUp hMint
        have e : Real.sqrt Real.pi * (K' * (2 + 2 ^ p) * U ^ p) =
            Real.sqrt Real.pi * (K' * (2 + 2 ^ p)) * U ^ p := by ring
        rw [e]
        linarith
    _ = K₀ * (1 + Real.sqrt Real.pi * (K' * (2 + 2 ^ p)) + Mint) * U ^ p := by ring

end Cubic.Analysis.MeanValueExtension
