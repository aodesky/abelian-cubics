import Cubic.Analysis.MeanValueExtension

/-!
The direct Gaussian residue argument in `lemma:xiMeanValue`.
The contour integrand is `ζ_E(w) exp((w-s)^2)/(w-s)`, with both
residues, at `s` and at `1`, retained explicitly.
-/

noncomputable section

namespace Cubic.Analysis.GaussianResidue

open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData
open Cubic.PoissonSummation
open Cubic.PoissonSummation.RectangleResidue
open Cubic.Analysis.MeanValueExtension
open scoped Interval

/-- Residues of an entire numerator divided by two distinct linear factors. -/
lemma rectangle_two_poles {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {z z' a b : ℂ} (hab : a ≠ b) (hRe : z.re ≤ z'.re) (hIm : z.im ≤ z'.im)
    (ha : Rectangle z z' ∈ 𝓝 a) (hb : Rectangle z z' ∈ 𝓝 b) :
    RectangleIntegral (fun w => F w / ((w - a) * (w - b))) z z' =
      2 * Real.pi * I * (F a / (a - b) + F b / (b - a)) := by
  let g := dslope (dslope F a) b
  have hg : DifferentiableOn ℂ g Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hF.differentiableOn)
  let A := F a / (a - b)
  let B := F b / (b - a)
  have hna : ∀ w ∈ RectangleBorder z z', w ≠ a := by
    intro w hw h; subst w
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds ha hw
  have hnb : ∀ w ∈ RectangleBorder z z', w ≠ b := by
    intro w hw h; subst w
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds hb hw
  have hca : ContinuousOn (fun w => A / (w - a)) (RectangleBorder z z') :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun w hw => sub_ne_zero.mpr (hna w hw))
  have hcb : ContinuousOn (fun w => B / (w - b)) (RectangleBorder z z') :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun w hw => sub_ne_zero.mpr (hnb w hw))
  have hcg : ContinuousOn g (RectangleBorder z z') :=
    hg.continuousOn.mono (subset_univ _)
  have heq : EqOn (fun w => F w / ((w - a) * (w - b)))
      ((g + fun w => A / (w - a)) + fun w => B / (w - b)) (RectangleBorder z z') := by
    intro w hw
    dsimp only [Pi.add_apply, g, A, B]
    rw [dslope_of_ne _ (hnb w hw), slope_def_field,
      dslope_of_ne _ (hna w hw), slope_def_field,
      dslope_of_ne _ hab.symm, slope_def_field]
    have hwa := sub_ne_zero.mpr (hna w hw)
    have hwb := sub_ne_zero.mpr (hnb w hw)
    have hab' := sub_ne_zero.mpr hab
    have hba := sub_ne_zero.mpr hab.symm
    field_simp
    <;> ring
  rw [RectangleIntegral_congr heq,
    RectangleBorderIntegrable.add (hcg.add hca).rectangleBorder_integrable hcb.rectangleBorder_integrable,
    RectangleBorderIntegrable.add hcg.rectangleBorder_integrable hca.rectangleBorder_integrable,
    HolomorphicOn.vanishesOnRectangle hg (subset_univ _), zero_add]
  have ha' := ResidueTheoremInRectangle (c := A) hRe hIm ha
  have hb' := ResidueTheoremInRectangle (c := B) hRe hIm hb
  simp only [RectangleIntegral', smul_eq_mul] at ha' hb'
  have hn : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hea : RectangleIntegral (fun w => A / (w - a)) z z' = 2 * Real.pi * I * A := by
    have := congrArg (fun x : ℂ => (2 * Real.pi * I) * x) ha'
    simpa only [← mul_assoc, mul_one_div_cancel hn, one_mul] using this
  have heb : RectangleIntegral (fun w => B / (w - b)) z z' = 2 * Real.pi * I * B := by
    have := congrArg (fun x : ℂ => (2 * Real.pi * I) * x) hb'
    simpa only [← mul_assoc, mul_one_div_cancel hn, one_mul] using this
  rw [hea, heb, ← mul_add]

/-- The entire numerator `(w-1) ζ_E(w)`, including its value at `1`. -/
def numerator (w : ℂ) : ℂ :=
  zetaOne w * DirichletCharacter.LFunction QuadraticDirichletCharacter.character w

lemma differentiable_numerator : Differentiable ℂ numerator :=
  differentiable_zetaOne.mul QuadraticDirichletCharacter.differentiable_LFunction

lemma numerator_eq {w : ℂ} (hw : w ≠ 1) : numerator w = (w - 1) * zetaE w := by
  simp only [numerator, zetaOne, Function.update_of_ne hw, zetaE]
  ring

/-- The residue of `ζ_E` at `1`. -/
def residue : ℂ := DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1

lemma numerator_one : numerator 1 = residue := by simp [numerator, zetaOne, residue]

def poleTerm (s : ℂ) : ℂ := residue * Complex.exp ((1 - s) ^ 2) / (1 - s)

def kernelIntegrand (s w : ℂ) : ℂ := zetaE w * Complex.exp ((w - s) ^ 2) / (w - s)

/-- The finite rectangle formula with both residues. Centering the horizontal
sides at `Im s` gives the same limit as the rectangles centered at zero. -/
lemma rectangle_residue {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 3)
    (hs : s ≠ 1) {R : ℝ} (hR : |s.im| < R) :
    RectangleIntegral (kernelIntegrand s)
      ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I)
      ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I) =
      2 * Real.pi * I * (zetaE s + poleTerm s) := by
  set z : ℂ := (1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I
  set z' : ℂ := (3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hzim : z.im = s.im - R := by simp [z]
  have hz're : z'.re = 3 := by simp [z']
  have hz'im : z'.im = s.im + R := by simp [z']
  have hR0 : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hRe : z.re ≤ z'.re := by rw [hzre, hz're]; norm_num
  have hIm : z.im ≤ z'.im := by rw [hzim, hz'im]; linarith
  have hmem : Rectangle z z' ∈ 𝓝 s := by
    rw [rectangle_mem_nhds_iff, hzre, hz're, hzim, hz'im,
      uIoo_of_le (by norm_num), uIoo_of_le (by linarith)]
    exact ⟨⟨hs1, hs2⟩, ⟨by linarith, by linarith⟩⟩
  have hmem1 : Rectangle z z' ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, hzre, hz're, hzim, hz'im,
      uIoo_of_le (by norm_num), uIoo_of_le (by linarith)]
    exact ⟨⟨by norm_num, by norm_num⟩,
      ⟨by simp only [one_im]; linarith [le_abs_self s.im],
       by simp only [one_im]; linarith [neg_abs_le s.im]⟩⟩
  let F : ℂ → ℂ := fun w => numerator w * Complex.exp ((w - s) ^ 2)
  have hF : Differentiable ℂ F := differentiable_numerator.mul (by fun_prop)
  have key := rectangle_two_poles hF hs hRe hIm hmem hmem1
  have heq : EqOn (kernelIntegrand s)
      (fun w => F w / ((w - s) * (w - 1))) (RectangleBorder z z') := by
    intro w hw
    have hw1 : w ≠ 1 := by
      intro h; subst w
      exact not_mem_rectangleBorder_of_rectangle_mem_nhds hmem1 hw
    simp only [kernelIntegrand, F, numerator_eq hw1]
    have h1 := sub_ne_zero.mpr hw1
    field_simp
    <;> ring
  rw [RectangleIntegral_congr heq, key]
  congr 1
  simp only [F, numerator_eq hs, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.exp_zero, mul_one, numerator_one, poleTerm]
  have hs' := sub_ne_zero.mpr hs
  field_simp

/-- Absolute convergence bounds the genuine zeta function on the right line. -/
lemma norm_zetaE_three_le : ∃ B : ℝ, ∀ v : ℝ, ‖zetaE ((3 : ℂ) + v * I)‖ ≤ B := by
  set S := ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) 3 n‖
  refine ⟨S * S, fun v => ?_⟩
  set w : ℂ := (3 : ℂ) + v * I
  have hre : w.re = 3 := by simp [w]
  have hζ : ‖riemannZeta w‖ ≤ S := by
    rw [← LSeries_one_eq_riemannZeta (by rw [hre]; norm_num)]
    exact norm_LSeries_le_of_re_eq_three _ (fun n => by simp) hre
  have hL : ‖DirichletCharacter.LFunction QuadraticDirichletCharacter.character w‖ ≤ S := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ (by rw [hre]; norm_num)]
    exact norm_LSeries_le_of_re_eq_three _ (fun n => DirichletCharacter.norm_le_one _ _) hre
  change ‖zetaE w‖ ≤ S * S
  rw [zetaE, norm_mul]
  exact mul_le_mul hζ hL (norm_nonneg _) ((norm_nonneg _).trans hζ)

lemma norm_kernelIntegrand (s w : ℂ) :
    ‖kernelIntegrand s w‖ =
      ‖zetaE w‖ * Real.exp ((w.re - s.re) ^ 2 - (w.im - s.im) ^ 2) / ‖w - s‖ := by
  rw [kernelIntegrand, norm_div, norm_mul, Complex.norm_exp]
  congr 3
  simp [pow_two, mul_re]

/-- The right side `Re w = 3`. -/
lemma norm_kernel_right_le {B : ℝ} (hB : ∀ v : ℝ, ‖zetaE ((3 : ℂ) + v * I)‖ ≤ B) {s : ℂ}
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
  calc ‖zetaE w‖ * Real.exp ((3 - s.re) ^ 2 - (v - s.im) ^ 2)
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
  calc ‖zetaE w‖ * Real.exp ((1 / 2 - s.re) ^ 2 - (v - s.im) ^ 2)
      ≤ ‖zetaE w‖ * (Real.exp 3 * Real.exp (-(v - s.im) ^ 2)) := by
        gcongr
    _ = Real.exp 3 / δ * (Real.exp (-(v - s.im) ^ 2) * ‖zetaE w‖) * δ := by
        field_simp
    _ ≤ Real.exp 3 / δ * (Real.exp (-(v - s.im) ^ 2) * ‖zetaE w‖) * ‖w - s‖ := by
        gcongr

/-- Polynomial growth on the horizontal edges, which stay at distance at least
one from the pole of `ζ_E`. -/
lemma norm_kernel_horizontal_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 → ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4)
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) {R y : ℝ} (hR : 1 ≤ R)
    (hy : |y - s.im| = R) (hy1 : 1 ≤ |y|) {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 3) :
    ‖kernelIntegrand s ((u : ℂ) + y * I)‖ ≤
      C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) := by
  set w : ℂ := (u : ℂ) + y * I
  have hre : w.re = u := by simp [w]
  have him : w.im = y := by simp [w]
  have hdist : R ≤ ‖w - s‖ := by
    have := Complex.abs_im_le_norm (w - s)
    rwa [sub_im, him, hy] at this
  have hw1 : 1 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    simp only [sub_im, him, one_im, sub_zero] at this
    exact hy1.trans this
  have hyle : |y| ≤ |s.im| + R := by
    have := abs_sub_abs_le_abs_sub y s.im
    linarith
  have hh : ‖zetaE w‖ ≤ C * (1 + |s.im| + R) ^ 4 := by
    have h1 := hC w (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him, norm_mul] at h1
    have h2 : C * (1 + |y|) ^ 4 ≤ C * (1 + |s.im| + R) ^ 4 := by
      gcongr C * ?_ ^ 4
      linarith
    nlinarith [norm_nonneg (zetaE w)]
  have hexp : Real.exp ((u - s.re) ^ 2 - (y - s.im) ^ 2) ≤
      Real.exp 7 * Real.exp (-R ^ 2) := by
    rw [← Real.exp_add]
    gcongr
    have : (y - s.im) ^ 2 = R ^ 2 := by rw [← hy, sq_abs]
    rw [this]
    nlinarith
  rw [norm_kernelIntegrand, hre, him, div_le_iff₀ (by linarith)]
  have hK0 : 0 ≤ C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) := by
    positivity
  calc ‖zetaE w‖ * Real.exp ((u - s.re) ^ 2 - (y - s.im) ^ 2)
      ≤ C * (1 + |s.im| + R) ^ 4 * (Real.exp 7 * Real.exp (-R ^ 2)) := by
        gcongr
    _ = C * (1 + |s.im| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2) * 1 := by ring
    _ ≤ _ := by gcongr; linarith

/-- `rectangle_residue` with the four sides written out. -/
lemma rectangle_residue' {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 3) (hs : s ≠ 1) {R : ℝ} (hR : |s.im| < R) :
    (∫ x in (1 / 2 : ℝ)..3, kernelIntegrand s ((x : ℂ) + ((s.im - R : ℝ) : ℂ) * I)) -
      (∫ x in (1 / 2 : ℝ)..3, kernelIntegrand s ((x : ℂ) + ((s.im + R : ℝ) : ℂ) * I)) +
      I * (∫ y in (s.im - R)..(s.im + R), kernelIntegrand s ((3 : ℂ) + y * I)) -
      I * (∫ y in (s.im - R)..(s.im + R), kernelIntegrand s ((1 / 2 : ℂ) + y * I)) =
      2 * Real.pi * I * (zetaE s + poleTerm s) := by
  have key := rectangle_residue hs1 hs2 hs hR
  have e1 : ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I).re = 1 / 2 := by simp
  have e2 : ((1 / 2 : ℂ) + ((s.im - R : ℝ) : ℂ) * I).im = s.im - R := by simp
  have e3 : ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I).re = 3 := by simp
  have e4 : ((3 : ℂ) + ((s.im + R : ℝ) : ℂ) * I).im = s.im + R := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, e1, e2, e3, e4, smul_eq_mul] at key
  have c3 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  have c12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  rw [c3, c12] at key
  exact key

/-- Cauchy's formula, after letting the rectangle grow:
`2π |ζ_E(s) + r exp((1-s)²)/(1-s)| ≤ A + (e³/δ) ∫ e^{-(v-t)²} |ζ_E(1/2+iv)| dv`. -/
lemma two_pi_norm_residues_le (hG : Growth) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → s ≠ 1 →
      2 * Real.pi * ‖(zetaE s + poleTerm s)‖ ≤ A + Real.exp 3 / δ *
        ∫ v : ℝ, Real.exp (-(v - s.im) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := hG.nonneg_const
  obtain ⟨B, hB⟩ := norm_zetaE_three_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B * Real.exp 7 * Real.sqrt Real.pi, by positivity, fun s hs1 hs2 hs => ?_⟩
  set t := s.im with ht
  set J := ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖
  set err : ℝ → ℝ := fun R => C * (1 + |t| + R) ^ 4 * Real.exp 7 * Real.exp (-R ^ 2)
  have hbound : ∀ R : ℝ, |t| + 1 ≤ R →
      2 * Real.pi * ‖(zetaE s + poleTerm s)‖ ≤ 5 / 2 * err R + 5 / 2 * err R +
        B * Real.exp 7 * Real.sqrt Real.pi + Real.exp 3 / δ * J := by
    intro R hR
    have hR1 : 1 ≤ R := by linarith [abs_nonneg t]
    have hR0 : 0 < R := by linarith
    have key := rectangle_residue' (s := s) (by linarith) (by linarith) hs (by change |t| < R; linarith)
    have hlhs : ‖2 * (Real.pi : ℂ) * I * (zetaE s + poleTerm s)‖ = 2 * Real.pi * ‖(zetaE s + poleTerm s)‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    -- horizontal sides
    have hH : ∀ y : ℝ, |y - t| = R → 1 ≤ |y| →
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
      (by rw [abs_of_neg (by linarith [le_abs_self t])]; linarith [le_abs_self t])
    have hH2 := hH (t + R) (by rw [add_sub_cancel_left, abs_of_pos hR0])
      (by rw [abs_of_pos (by linarith [neg_abs_le t])]; linarith [neg_abs_le t])
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


/-- The residue contribution is uniformly bounded for `|Im s| ≥ 2`. -/
lemma norm_poleTerm_le {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) : ‖poleTerm s‖ ≤ ‖residue‖ := by
  have hd : 2 ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at this
    exact ht.trans this
  have he : ((1 - s) ^ 2).re = (1 - s.re) ^ 2 - s.im ^ 2 := by
    simp [pow_two, mul_re]
  have ht2 : 4 ≤ s.im ^ 2 := by nlinarith [sq_abs s.im]
  have hexp : Real.exp (((1 - s) ^ 2).re) ≤ 1 := by
    rw [Real.exp_le_one_iff, he]
    nlinarith
  rw [poleTerm, norm_div, norm_mul, Complex.norm_exp, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg residue]

/-- The Gaussian bound for `ζ_E`, including the bounded residue term. -/
lemma two_pi_norm_zetaE_le (hG : Growth) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      2 * Real.pi * ‖zetaE s‖ ≤ A + Real.exp 3 / δ *
        ∫ v : ℝ, Real.exp (-(v - s.im) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * I)‖ := by
  obtain ⟨A, hA0, hA⟩ := two_pi_norm_residues_le hG hδ
  refine ⟨A + 2 * Real.pi * ‖residue‖, by positivity, fun s hs1 hs2 ht => ?_⟩
  have hs : s ≠ 1 := by intro h; norm_num [h] at ht
  have hbound := hA s hs1 hs2 hs
  have hp := norm_poleTerm_le (by linarith) hs2 ht
  have hn := norm_sub_le (zetaE s + poleTerm s) (poleTerm s)
  rw [add_sub_cancel_right] at hn
  nlinarith [Real.pi_pos]

/-- The pointwise bound, with a nonnegative constant. -/
theorem pointwise_nonneg (hG : Growth) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ t : ℝ, 2 ≤ t →
      ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤
        K * (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * ‖zetaE ((1 / 2 : ℂ) + v * Complex.I)‖ ^ 2) := by
  obtain ⟨A, hA0, hA⟩ := two_pi_norm_zetaE_le hG hδ
  have hp : 0 < 2 * Real.pi := by positivity
  set a := A / (2 * Real.pi)
  set b := (Real.exp 3 / δ * ((Real.sqrt Real.pi + 1) / 2)) / (2 * Real.pi)
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
  have hh := hA s (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
    (by rw [him, abs_of_nonneg (by linarith)]; exact ht)
  rw [him] at hh
  have hζ' : ‖zetaE s‖ ≤ a + b * l := by
    have h1 : ‖zetaE s‖ ≤ (A + Real.exp 3 / δ * J) / (2 * Real.pi) := by
      rw [le_div_iff₀ hp]; linarith
    calc ‖zetaE s‖ ≤ (A + Real.exp 3 / δ * (l * (Real.sqrt Real.pi + 1) / 2)) /
          (2 * Real.pi) := by
          refine h1.trans ?_
          gcongr
      _ = a + b * l := by simp only [a, b]; field_simp
  calc ‖zetaE s‖ ^ 2 ≤ (a + b * l) ^ 2 := by gcongr
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 * l ^ 2 := by nlinarith [sq_nonneg (a - b * l)]
    _ = 2 * a ^ 2 + 2 * b ^ 2 * (1 + I₂) := by rw [hl2]
    _ ≤ (2 * a ^ 2 + 2 * b ^ 2) * (1 + I₂) := by nlinarith [sq_nonneg a]

end Cubic.Analysis.GaussianResidue
