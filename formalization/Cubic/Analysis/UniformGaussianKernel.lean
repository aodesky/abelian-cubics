import Cubic.Analysis.PoissonGaussianWeight

/-!
Cauchy's formula with the reflected point `1-conj(s)` outside the strip.
The extra factor changes the critical-line kernel into a Poisson kernel,
whose mass stays bounded as `Re(s)` approaches `1/2`.
-/
noncomputable section
namespace Cubic.Analysis.UniformGaussianKernel
open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData Cubic.Analysis.MeanValueExtension
open Cubic.PoissonSummation Cubic.PoissonSummation.RectangleResidue

def reflected (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s
@[simp] lemma reflected_re (s : ℂ) : (reflected s).re = 1 - s.re := by simp [reflected]
@[simp] lemma reflected_im (s : ℂ) : (reflected s).im = s.im := by simp [reflected]

def kernelIntegrand (s w : ℂ) : ℂ :=
  MeanValueExtension.kernelIntegrand s w * ((s - reflected s) / (w - reflected s))

lemma norm_sub_reflected {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖s - reflected s‖ = 2 * (s.re - 1 / 2) := by
  have he : s - reflected s = ((2 * (s.re - 1 / 2) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

lemma rectangle_cauchy {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re ≤ 2)
    {R : ℝ} (hR : 0 < R) :
    RectangleIntegral (kernelIntegrand s)
      ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I)
      ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I) =
      2 * Real.pi * I * hfun s := by
  set z : ℂ := (1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I
  set z' : ℂ := (3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hzim : z.im = s.im - R := by simp [z]
  have hz're : z'.re = 3 := by simp [z']
  have hz'im : z'.im = s.im + R := by simp [z']
  let S : Set ℂ := {w | (reflected s).re < w.re}
  let F : ℂ → ℂ := fun w => hfun w * Complex.exp ((w - s) ^ 2) *
    ((s - reflected s) / (w - reflected s))
  have hS : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hsS : S ∈ 𝓝 s := hS.mem_nhds (by dsimp [S]; simp; linarith)
  have hne (w : ℂ) (hw : w ∈ S) : w - reflected s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    have : (reflected s).re < w.re := hw
    simp at this
    linarith
  have hF : DifferentiableOn ℂ F S := by
    refine (differentiableOn_hfun.mono (fun w hw => ?_)).mul (by fun_prop) |>.mul ?_
    · dsimp [S] at hw
      simp at hw
      change -2 < w.re
      linarith
    · exact DifferentiableOn.div (by fun_prop) (by fun_prop) hne
  have hg := (Complex.differentiableOn_dslope hsS).mpr hF
  have hrect : Rectangle z z' ⊆ S := by
    intro w hw
    have h1 := hw.1
    rw [hzre, hz're, uIcc_of_le (by norm_num)] at h1
    dsimp [S]; simp
    linarith [h1.1]
  have hmem : Rectangle z z' ∈ 𝓝 s := by
    rw [rectangle_mem_nhds_iff, hzre, hz're, hzim, hz'im,
      uIoo_of_le (by norm_num), uIoo_of_le (by linarith)]
    exact ⟨⟨hs1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hss : s - reflected s ≠ 0 := hne s (by dsimp [S]; simp; linarith)
  have hFs : F s = hfun s := by simp [F, hss]
  have key := ResidueTheoremOnRectangleWithSimplePole (f := kernelIntegrand s)
    (g := dslope F s) (A := hfun s)
    (by rw [hzre, hz're]; norm_num) (by rw [hzim, hz'im]; linarith)
    hmem (hg.mono hrect) ?_
  · rw [RectangleIntegral', smul_eq_mul] at key
    rw [← key]
    have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp
  · intro w hw
    rw [dslope_of_ne _ hw.2, slope_def_field, hFs]
    dsimp [kernelIntegrand, MeanValueExtension.kernelIntegrand, F]
    have hws := sub_ne_zero.mpr hw.2
    have hwm := hne w (hrect hw.1)
    field_simp
    <;> ring

lemma norm_factor_le {s w : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2)
    (hw : 1 ≤ ‖w - reflected s‖) : ‖(s - reflected s) / (w - reflected s)‖ ≤ 3 := by
  rw [norm_div, norm_sub_reflected hs1, div_le_iff₀ (by linarith)]
  linarith

lemma norm_kernel_right_le {B : ℝ} (hB : ∀ v : ℝ, ‖hfun ((3 : ℂ) + v * I)‖ ≤ B)
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) (v : ℝ) :
    ‖kernelIntegrand s ((3 : ℂ) + v * I)‖ ≤
      3 * B * Real.exp 7 * Real.exp (-(v - s.im) ^ 2) := by
  have hd : 1 ≤ ‖((3 : ℂ) + v * I) - reflected s‖ := by
    have h := Complex.abs_re_le_norm (((3 : ℂ) + v * I) - reflected s)
    simp at h
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  have hh := MeanValueExtension.norm_kernel_right_le hB hs1 hs2 v
  rw [kernelIntegrand, norm_mul]
  calc _ ≤ (B * Real.exp 7 * Real.exp (-(v - s.im) ^ 2)) * 3 :=
      mul_le_mul hh (norm_factor_le hs1 hs2 hd) (norm_nonneg _)
        ((norm_nonneg _).trans hh)
    _ = _ := by ring

lemma norm_kernel_horizontal_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 →
      ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4)
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) {R y : ℝ} (hR : 1 ≤ R)
    (hy : |y - s.im| = R) (hy0 : y ≠ 0) {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 3) :
    ‖kernelIntegrand s ((u : ℂ) + y * I)‖ ≤
      (3 * C) * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) := by
  have hd : 1 ≤ ‖((u : ℂ) + y * I) - reflected s‖ := by
    have h := Complex.abs_im_le_norm (((u : ℂ) + y * I) - reflected s)
    have hh : |y - s.im| ≤ ‖((u : ℂ) + y * I) - reflected s‖ := by simpa using h
    rw [hy] at hh
    exact hR.trans hh
  have hh := MeanValueExtension.norm_kernel_horizontal_le hC0 hC hs1 hs2 hR hy hy0 hu1 hu2
  rw [kernelIntegrand, norm_mul]
  calc _ ≤ (C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)) * 3 :=
      mul_le_mul hh (norm_factor_le hs1 hs2 hd) (norm_nonneg _)
        ((norm_nonneg _).trans hh)
    _ = _ := by ring

lemma norm_kernel_left_le {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re ≤ 2) (v : ℝ) :
    ‖kernelIntegrand s ((1 / 2 : ℂ) + v * I)‖ ≤
      (2 * Real.exp 3) * (PoissonGaussianWeight.weight (s.re - 1 / 2) (v - s.im) *
        ‖zetaE ((1 / 2 : ℂ) + v * I)‖) := by
  set w : ℂ := (1 / 2 : ℂ) + v * I
  have hre : w.re = 1 / 2 := by simp [w]
  have him : w.im = v := by simp [w]
  have hsq : ‖w - s‖ ^ 2 = (s.re - 1 / 2) ^ 2 + (v - s.im) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, hre, him]
    ring
  have he : ‖w - reflected s‖ = ‖w - s‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, hre, him]
    ring
  have hprod : ‖w - s‖ * ‖w - reflected s‖ =
      (s.re - 1 / 2) ^ 2 + (v - s.im) ^ 2 := by rw [he, ← pow_two, hsq]
  have hexp : Real.exp ((1 / 2 - s.re) ^ 2 - (v - s.im) ^ 2) ≤
      Real.exp 3 * Real.exp (-(v - s.im) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [kernelIntegrand, norm_mul, norm_div, MeanValueExtension.norm_kernelIntegrand,
    norm_sub_reflected hs1.le, hre, him, div_mul_div_comm, hprod]
  calc _ ≤ (‖zetaE w‖ * (Real.exp 3 * Real.exp (-(v - s.im) ^ 2)) *
        (2 * (s.re - 1 / 2))) / ((s.re - 1 / 2) ^ 2 + (v - s.im) ^ 2) := by
          gcongr
          · linarith
          · exact norm_hfun_le_norm_zetaE_of_re hre
    _ = _ := by unfold PoissonGaussianWeight.weight; ring

lemma rectangle_cauchy' {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re ≤ 2) {R : ℝ} (hR : 0 < R) :
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

lemma two_pi_norm_hfun_le (hG : Growth) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 →
      2 * Real.pi * ‖hfun s‖ ≤ A + (2 * Real.exp 3) *
        ∫ v : ℝ, PoissonGaussianWeight.weight (s.re - 1 / 2) (v - s.im) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := hG.nonneg_const
  obtain ⟨B, hB⟩ := norm_hfun_three_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨3 * B * Real.exp 7 * Real.sqrt Real.pi, by positivity, fun s hs1 hs2 => ?_⟩
  set t := s.im with ht
  set J := ∫ v : ℝ, PoissonGaussianWeight.weight (s.re - 1 / 2) (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
  set err : ℝ → ℝ := fun R => (3 * C) * (1 + |t| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)
  have hbound : ∀ R : ℝ, |t| + 1 ≤ R →
      2 * Real.pi * ‖hfun s‖ ≤ 5 / 2 * err R + 5 / 2 * err R +
        3 * B * Real.exp 7 * Real.sqrt Real.pi + (2 * Real.exp 3) * J := by
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
        3 * B * Real.exp 7 * Real.sqrt Real.pi := by
      have hg : Integrable fun y : ℝ => 3 * B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
        (integrable_gauss_shift t).const_mul _
      calc _ ≤ ∫ y in (t - R)..(t + R), 3 * B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
            intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun y _ => norm_kernel_right_le hB (by linarith) hs2 y)
              hg.intervalIntegrable
        _ ≤ ∫ y, 3 * B * Real.exp 7 * Real.exp (-(y - t) ^ 2) :=
            intervalIntegral_le_integral hg (fun y => by positivity) (by linarith)
        _ = 3 * B * Real.exp 7 * Real.sqrt Real.pi := by
            rw [integral_const_mul, integral_gauss_shift]
    -- left side
    have hVh : ‖∫ y in (t - R)..(t + R), kernelIntegrand s ((1 / 2 : ℂ) + y * I)‖ ≤
        (2 * Real.exp 3) * J := by
      have hg : Integrable fun y : ℝ => (2 * Real.exp 3) *
          (PoissonGaussianWeight.weight (s.re - 1 / 2) (y - t) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
        (PoissonGaussianWeight.integrable_zeta hG (by linarith : 0 < s.re - 1 / 2) t).const_mul _
      calc _ ≤ ∫ y in (t - R)..(t + R), (2 * Real.exp 3) *
              (PoissonGaussianWeight.weight (s.re - 1 / 2) (y - t) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
            intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun y _ => norm_kernel_left_le hs1 hs2 y)
              hg.intervalIntegrable
        _ ≤ ∫ y, (2 * Real.exp 3) *
              (PoissonGaussianWeight.weight (s.re - 1 / 2) (y - t) * ‖zetaE ((1 / 2 : ℂ) + y * I)‖) :=
            intervalIntegral_le_integral hg (fun y => mul_nonneg (by positivity)
              (mul_nonneg (PoissonGaussianWeight.nonneg (by linarith) _) (norm_nonneg _))) (by linarith)
        _ = (2 * Real.exp 3) * J := by rw [integral_const_mul]
    rw [← hlhs, ← key]
    refine (norm_four_le _ _ _ _).trans ?_
    rw [norm_mul, norm_mul, norm_I, one_mul, one_mul]
    linarith
  have hlim : Tendsto (fun R => 5 / 2 * err R + 5 / 2 * err R +
      3 * B * Real.exp 7 * Real.sqrt Real.pi + (2 * Real.exp 3) * J) atTop
      (𝓝 (5 / 2 * 0 + 5 / 2 * 0 + 3 * B * Real.exp 7 * Real.sqrt Real.pi + (2 * Real.exp 3) * J)) := by
    have h := tendsto_horizontal_error (show 0 ≤ 3 * C by positivity) (abs_nonneg t)
    exact ((((h.const_mul _).add (h.const_mul _)).add_const _).add_const _)
  have := ge_of_tendsto hlim ((eventually_ge_atTop (|t| + 1)).mono hbound)
  simpa using this


theorem pointwise_nonneg (hG : Growth) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 2 → ∀ t : ℝ, 2 ≤ t →
      ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤
        K * (1 + ∫ v : ℝ, PoissonGaussianWeight.weight (σ - 1 / 2) (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * Complex.I)‖ ^ 2) := by
  obtain ⟨A, hA0, hA⟩ := two_pi_norm_hfun_le hG
  have hp : 0 < 2 * Real.pi := by positivity
  set a := 5 / 2 * A / (2 * Real.pi)
  set b := 5 / 2 * ((2 * Real.exp 3) * ((Real.pi + 1) / 2)) / (2 * Real.pi)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  refine ⟨2 * a ^ 2 + 2 * b ^ 2, by positivity, fun σ hσ1 hσ2 t ht => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  set I₂ := ∫ v : ℝ, PoissonGaussianWeight.weight (σ - 1 / 2) (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2
  set J := ∫ v : ℝ, PoissonGaussianWeight.weight (σ - 1 / 2) (v - t) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun v =>
    mul_nonneg (PoissonGaussianWeight.nonneg (by linarith : 0 < σ - 1 / 2) _) (sq_nonneg _)
  set l := Real.sqrt (1 + I₂)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hl2 : l ^ 2 = 1 + I₂ := Real.sq_sqrt (by linarith)
  have hJ : J ≤ l * (Real.pi + 1) / 2 := PoissonGaussianWeight.cauchy_schwarz hG (by linarith : 0 < σ - 1 / 2) t
  -- `2π |h(s)| ≤ A + 2 e³ J`, with a constant independent of σ.
  have hh := hA s (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
  rw [him, hre] at hh
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
    have h1 : ‖hfun s‖ ≤ (A + (2 * Real.exp 3) * J) / (2 * Real.pi) := by
      rw [le_div_iff₀ hp]; linarith
    have h2 : A + (2 * Real.exp 3) * J ≤
        A + (2 * Real.exp 3) * (l * (Real.pi + 1) / 2) := by gcongr
    calc ‖zetaE s‖ ≤ 5 / 2 * ((A + (2 * Real.exp 3) * (l * (Real.pi + 1) / 2)) /
          (2 * Real.pi)) := by
          refine hζ.trans ?_
          gcongr
          exact h1.trans (by gcongr)
      _ = a + b * l := by simp only [a, b]; field_simp
  calc ‖zetaE s‖ ^ 2 ≤ (a + b * l) ^ 2 := by gcongr
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 * l ^ 2 := by nlinarith [sq_nonneg (a - b * l)]
    _ = 2 * a ^ 2 + 2 * b ^ 2 * (1 + I₂) := by rw [hl2]
    _ ≤ (2 * a ^ 2 + 2 * b ^ 2) * (1 + I₂) := by nlinarith [sq_nonneg a]


end Cubic.Analysis.UniformGaussianKernel
