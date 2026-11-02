import Cubic.PoissonSummation.HeightZetaContourDecay
import Cubic.PoissonSummation.RectangleResidue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Closing the height-zeta contour in the upper half-plane

Apply the simple-pole residue theorem to the actual continued Fourier
integrand. The holomorphic remainder is the divided difference of its
numerator; thus its regularity at the pole is proved, not assumed.

We use a rectangular upper closure to reuse the focused PNT+ backport.
This changes the contour's shape from the paper's semicircle, while retaining
its pole, orientation, residue and quadratic-decay argument. The semicircle
estimate remains separately proved in `HeightZetaContourDecay`.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContourIntegral

open Complex MeasureTheory Filter HeightZetaResidue FiniteEulerProduct
open HeightZetaFormulaData HeightZetaContourDecay RectangleResidue
open scoped Topology

/-- Remove the upper-pole denominator, keeping the finite transform. -/
def numerator (s₀ σ t : ℂ) : ℂ :=
  ((s₀ + 2 * σ) / ((2 * Real.pi * I) * (2 * σ - 2 * Real.pi * I * t))) *
    value (complexSpectralParameter σ t)

private theorem scale_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

theorem differentiableAt_numerator (s₀ σ t : ℂ) (hσ : 1 < σ.re) (ht : 0 ≤ t.im) :
    DifferentiableAt ℂ (numerator s₀ σ) t := by
  have hne : t ≠ lowerPole σ := by
    intro he
    rw [he] at ht
    exact (lowerPole_neg σ (lt_trans zero_lt_one hσ)).not_ge ht
  have hd : (2 * Real.pi * I) * (2 * σ - 2 * Real.pi * I * t) ≠ 0 := by
    rw [second_denominator]
    exact mul_ne_zero scale_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr scale_ne_zero) (sub_ne_zero.mpr hne))
  have ha : DifferentiableAt ℂ (fun w : ℂ =>
      (s₀ + 2 * σ) / ((2 * Real.pi * I) * (2 * σ - 2 * Real.pi * I * w))) t :=
    (differentiableAt_const _).div (by fun_prop) hd
  exact ha.mul (differentiableAt_upper_half_plane σ t hσ ht)

theorem numerator_at_upperPole (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    numerator s₀ σ (upperPole s₀) =
      (2 * Real.pi * I : ℂ)⁻¹ * value (parameter s₀ σ) := by
  have hn : s₀ + 2 * σ ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num [mul_re] at hr
    linarith
  rw [numerator, second_denominator_at_upperPole, parameter_at_upperPole]
  congr 1
  field_simp

theorem fullContinuation_eq_div (s₀ σ t : ℂ) (ht : t ≠ upperPole s₀) :
    fullContinuation s₀ σ t = numerator s₀ σ t / (t - upperPole s₀) := by
  apply (eq_div_iff (sub_ne_zero.mpr ht)).mpr
  simpa only [fullContinuation, numerator, mul_left_comm, mul_comm, mul_assoc] using
    congrArg (fun z => z * value (complexSpectralParameter σ t))
      (cancel_upperPole s₀ σ t ht)

/-- Exact principal part, with the remainder extended holomorphically by `dslope`. -/
theorem principalPart (s₀ σ : ℂ) :
    Set.EqOn (fullContinuation s₀ σ - fun t =>
        numerator s₀ σ (upperPole s₀) / (t - upperPole s₀))
      (dslope (numerator s₀ σ) (upperPole s₀)) {upperPole s₀}ᶜ := by
  intro t ht
  have hne : t ≠ upperPole s₀ := ht
  rw [Pi.sub_apply, fullContinuation_eq_div s₀ σ t hne, dslope_of_ne _ hne]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  ring

/-- The upper rectangle contains the pole once its radius exceeds the decay radius. -/
theorem upperPole_mem_rectangle (s₀ σ : ℂ) (h₀ : 0 < s₀.re)
    (R : ℝ) (hR : radius s₀ σ ≤ R) :
    Rectangle (-(R : ℂ)) (R + R * I) ∈ 𝓝 (upperPole s₀) := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  have hp : ‖upperPole s₀‖ < R := by
    dsimp [radius] at hR
    linarith [norm_nonneg s₀, norm_nonneg (2 * σ)]
  rw [rectangle_mem_nhds_iff]
  simp only [neg_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, sub_self, add_zero, zero_add, neg_im, neg_zero, add_im, mul_im,
    mul_one, mem_reProdIm]
  rw [Set.uIoo_of_lt (by linarith : -R < R), Set.uIoo_of_lt hR0]
  exact ⟨⟨by linarith [(abs_le.mp (abs_re_le_norm (upperPole s₀))).1],
    (re_le_norm _).trans_lt hp⟩, upperPole_pos s₀ h₀, (im_le_norm _).trans_lt hp⟩

/-- Counterclockwise integration gives `2πi` times the upper residue.
The finite factor `1/6` is still present in the answer. -/
theorem rectangle_integral (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re)
    (R : ℝ) (hR : radius s₀ σ ≤ R) :
    RectangleIntegral (fullContinuation s₀ σ) (-(R : ℂ)) (R + R * I) =
      value (parameter s₀ σ) := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  have hp := upperPole_mem_rectangle s₀ σ h₀ R hR
  have hn : DifferentiableOn ℂ (numerator s₀ σ)
      (Rectangle (-(R : ℂ)) (R + R * I)) := by
    intro t ht
    apply (differentiableAt_numerator s₀ σ t hσ ?_).differentiableWithinAt
    have hti : t.im ∈ Set.uIcc 0 R := by simpa using ht.2
    rw [Set.uIcc_of_le hR0.le] at hti
    exact hti.1
  have hg := (Complex.differentiableOn_dslope hp).mpr hn
  have hrect := ResidueTheoremOnRectangleWithSimplePole
    (f := fullContinuation s₀ σ) (g := dslope (numerator s₀ σ) (upperPole s₀))
    (by simp; linarith : (-(R : ℂ)).re ≤ (R + R * I).re)
    (by simpa using hR0.le : (-(R : ℂ)).im ≤ (R + R * I).im)
    hp hg ((principalPart s₀ σ).mono (fun _ hx => hx.2))
  rw [numerator_at_upperPole s₀ σ h₀ hσ] at hrect
  simp only [RectangleIntegral', smul_eq_mul, one_div] at hrect
  exact mul_left_cancel₀ (inv_ne_zero scale_ne_zero) hrect

/-- All four edge integrals are genuine integrals of continuous functions. -/
theorem rectangle_border_integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re)
    (R : ℝ) (hR : radius s₀ σ ≤ R) :
    RectangleBorderIntegrable (fullContinuation s₀ σ) (-(R : ℂ)) (R + R * I) := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  apply ContinuousOn.rectangleBorder_integrable
  intro t ht
  have hti : t.im ∈ Set.uIcc 0 R := by
    simpa using (rectangleBorder_subset_rectangle _ _ ht).2
  rw [Set.uIcc_of_le hR0.le] at hti
  exact (differentiableAt_fullContinuation s₀ σ t hσ hti.1 (by
    intro he
    subst t
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds
      (upperPole_mem_rectangle s₀ σ h₀ R hR) ht)).continuousAt.continuousWithinAt

/-- The three upper edges, with the same positive orientation as the rectangle. -/
def upperClosure (s₀ σ : ℂ) (R : ℝ) : ℂ :=
  -HIntegral (fullContinuation s₀ σ) (-R) R R +
    VIntegral (fullContinuation s₀ σ) R 0 R -
    VIntegral (fullContinuation s₀ σ) (-R) 0 R

private theorem full_bound (s₀ σ : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℂ, 0 ≤ t.im → ‖value (complexSpectralParameter σ t)‖ ≤ C)
    (R : ℝ) (hR : radius s₀ σ ≤ R) (t : ℂ) (ht : 0 ≤ t.im) (htR : R ≤ ‖t‖) :
    ‖fullContinuation s₀ σ t‖ ≤ 4 * ‖s₀ + 2 * σ‖ * C / R ^ 2 := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  rw [fullContinuation, norm_mul]
  calc
    _ ≤ (4 * ‖s₀ + 2 * σ‖ / ‖t‖ ^ 2) * C :=
      mul_le_mul (archimedean_bound s₀ σ t (hR.trans htR)) (hbound t ht)
        (norm_nonneg _) (by positivity)
    _ = 4 * ‖s₀ + 2 * σ‖ * C / ‖t‖ ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (sq_le_sq₀ hR0.le (norm_nonneg t) |>.mpr htR)

theorem upperClosure_norm_bound (s₀ σ : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℂ, 0 ≤ t.im → ‖value (complexSpectralParameter σ t)‖ ≤ C)
    (R : ℝ) (hR : radius s₀ σ ≤ R) :
    ‖upperClosure s₀ σ R‖ ≤ 16 * ‖s₀ + 2 * σ‖ * C / R := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  let B := 4 * ‖s₀ + 2 * σ‖ * C
  have htop : ‖HIntegral (fullContinuation s₀ σ) (-R) R R‖ ≤ 2 * B / R := by
    have hb : ∀ x ∈ Set.uIoc (-R) R,
        ‖fullContinuation s₀ σ (x + R * I)‖ ≤ B / R ^ 2 := by
      intro x _
      exact full_bound s₀ σ C hC hbound R hR _ (by simpa using hR0.le)
        (by simpa using im_le_norm ((x : ℂ) + R * I))
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show R - -R = 2 * R by ring, abs_of_pos (by positivity : 0 < 2 * R)] at hh
    calc
      _ ≤ B / R ^ 2 * (2 * R) := hh
      _ = _ := by field_simp
  have hvertical (x : ℝ) (hx : |x| = R) :
      ‖VIntegral (fullContinuation s₀ σ) x 0 R‖ ≤ B / R := by
    have hb : ∀ y ∈ Set.uIoc 0 R,
        ‖fullContinuation s₀ σ (x + y * I)‖ ≤ B / R ^ 2 := by
      intro y hy
      rw [Set.uIoc_of_le hR0.le] at hy
      exact full_bound s₀ σ C hC hbound R hR _ (by simpa using hy.1.le)
        (by simpa [hx] using abs_re_le_norm ((x : ℂ) + y * I))
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_pos hR0] at hh
    simp only [VIntegral, norm_smul, norm_I, one_mul]
    calc
      _ ≤ B / R ^ 2 * R := hh
      _ = _ := by field_simp
  have hright := hvertical R (abs_of_pos hR0)
  have hleft := hvertical (-R) (by rw [abs_neg, abs_of_pos hR0])
  calc
    ‖upperClosure s₀ σ R‖ ≤
        ‖HIntegral (fullContinuation s₀ σ) (-R) R R‖ +
          ‖VIntegral (fullContinuation s₀ σ) R 0 R‖ +
          ‖VIntegral (fullContinuation s₀ σ) (-R) 0 R‖ := by
      unfold upperClosure
      apply (norm_sub_le _ _).trans
      refine add_le_add ?_ le_rfl
      simpa only [norm_neg] using norm_add_le
        (-HIntegral (fullContinuation s₀ σ) (-R) R R)
        (VIntegral (fullContinuation s₀ σ) R 0 R)
    _ ≤ 2 * B / R + B / R + B / R := add_le_add (add_le_add htop hright) hleft
    _ = _ := by dsimp [B]; ring

theorem upperClosure_tendsto_zero (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Tendsto (upperClosure s₀ σ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := upper_half_plane_bound σ hσ
  apply squeeze_zero_norm' (a := fun R : ℝ => 16 * ‖s₀ + 2 * σ‖ * C / R)
  · filter_upwards [eventually_ge_atTop (radius s₀ σ)] with R hR
    exact upperClosure_norm_bound s₀ σ C hC hbound R hR
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- Residue evaluation of the original absolutely integrable spectral function. -/
theorem integral_eq_finite_value (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    (∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t) =
      value (parameter s₀ σ) := by
  have hi : Integrable (fun t : ℝ => fullContinuation s₀ σ t) := by
    simpa only [fullContinuation_ofReal s₀ σ _ h₀ hσ] using
      AdelicSpectralIntegrand.integrable s₀ σ h₀ hσ
  have hbottom := intervalIntegral_tendsto_integral hi
    (tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ => -R) atTop atBot) tendsto_id
  have hlimit := hbottom.add (upperClosure_tendsto_zero s₀ σ hσ)
  have heq : (fun R : ℝ => (∫ t in -R..R, fullContinuation s₀ σ t) +
      upperClosure s₀ σ R) =ᶠ[atTop] fun _ => value (parameter s₀ σ) := by
    filter_upwards [eventually_ge_atTop (radius s₀ σ)] with R hR
    convert rectangle_integral s₀ σ h₀ hσ R hR using 1
    simp [RectangleIntegral, HIntegral, VIntegral, upperClosure]
    ring
  have he := tendsto_nhds_unique hlimit (tendsto_const_nhds.congr' heq.symm)
  simpa only [add_zero, fullContinuation_ofReal s₀ σ _ h₀ hσ] using he

end Cubic.PoissonSummation.HeightZetaContourIntegral
