import Cubic.PoissonSummation.RectangleResidue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The truncated Perron kernel

For `y > 0`, `c > 0` and `T > 0` put
`I(y, c, T) = (1 / 2πi) ∫_{c - iT}^{c + iT} y^s / s ds`,
with the vertical segment parametrized by `s = c + it`, `-T ≤ t ≤ T`.

* `norm_kernel_sub_indicator_le`: for `y ≠ 1`,
  `|I(y, c, T) - 1_{y > 1}| ≤ y^c / (π T |log y|)`.
  The contour is moved to the right (`y < 1`) or to the left (`y > 1`, picking up the
  residue `1` at `s = 0`) with the rectangle Cauchy theorem; the horizontal sides are
  bounded using `|y^s / s| ≤ y^σ / T`, and the far vertical side tends to zero.
* `norm_kernel_sub_indicator_le_four`: for `0 < c ≤ 2`, `T ≥ 1` and every `y > 0`,
  `|I(y, c, T) - 1_{y > 1}| ≤ 4 y^c`.
  When `|log y| ≥ 1 / (4T)` this follows from the first bound; otherwise `I(y, c, T)`
  is compared with `I(1, c, T) = arctan (T / c) / π`.
-/

noncomputable section

namespace Cubic.Analysis.Perron

open Complex Set Filter Topology MeasureTheory intervalIntegral
open Cubic.PoissonSummation.RectangleResidue
open scoped Interval

/-- The integrand `y^s / s` of the Perron kernel. -/
def kernelIntegrand (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

/-- The truncated Perron kernel `(1 / 2πi) ∫_{c - iT}^{c + iT} y^s / s ds`,
written as a real integral over `s = c + it` with `ds = i dt`. -/
def kernel (y c T : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I

lemma kernel_eq_vIntegral (y c T : ℝ) :
    kernel y c T = (2 * Real.pi * I)⁻¹ * VIntegral (kernelIntegrand y) c (-T) T := by
  simp only [kernel, VIntegral, kernelIntegrand, smul_eq_mul, intervalIntegral.integral_mul_const]
  ring

lemma norm_kernelIntegrand {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖kernelIntegrand y s‖ = y ^ s.re / ‖s‖ := by
  rw [kernelIntegrand, norm_div, norm_cpow_eq_rpow_re_of_pos hy]

lemma differentiableAt_kernelIntegrand {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (kernelIntegrand y) s := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (differentiableAt_id.const_cpow (Or.inl hy')).div differentiableAt_id hs

lemma continuous_cpow_const_base {y : ℝ} (hy : 0 < y) : Continuous fun s : ℂ => (y : ℂ) ^ s := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact continuous_id.const_cpow (Or.inl hy')

lemma norm_pi_I_inv : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

/-- `∫_a^b y^x dx = (y^b - y^a) / log y`. -/
lemma integral_rpow_base {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (a b : ℝ) :
    ∫ x in a..b, y ^ x = (y ^ b - y ^ a) / Real.log y := by
  have hlog : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => y ^ x / Real.log y) (y ^ x) x := fun x => by
    have := ((Real.hasStrictDerivAt_const_rpow hy x).hasDerivAt).div_const (Real.log y)
    convert this using 1
    field_simp
  have hc : Continuous fun x : ℝ => y ^ x :=
    continuous_const.rpow continuous_id fun _ => Or.inl hy.ne'
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  ring

/-- Bound for a horizontal side at height `τ ≠ 0`. -/
lemma norm_hIntegral_le {y a b τ : ℝ} (hy : 0 < y) (hab : a ≤ b) (hτ : τ ≠ 0) :
    ‖HIntegral (kernelIntegrand y) a b τ‖ ≤ ∫ x in a..b, y ^ x / |τ| := by
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun x _ => ?_) ?_
  · rw [norm_kernelIntegrand hy]
    have him : |τ| ≤ ‖(x : ℂ) + τ * I‖ := by
      simpa using Complex.abs_im_le_norm ((x : ℂ) + τ * I)
    have hre : ((x : ℂ) + τ * I).re = x := by simp
    rw [hre]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (abs_pos.2 hτ) him
  · exact ((continuous_const.rpow continuous_id fun _ => Or.inl hy.ne').div_const
      _).intervalIntegrable _ _

/-- Bound for the vertical side at abscissa `a ≠ 0`. -/
lemma norm_vIntegral_le {y a T : ℝ} (hy : 0 < y) (ha : a ≠ 0) (hT : 0 ≤ T) :
    ‖VIntegral (kernelIntegrand y) a (-T) T‖ ≤ 2 * T * (y ^ a / |a|) := by
  rw [VIntegral, norm_smul, norm_I, one_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := y ^ a / |a|) (f := fun t : ℝ => kernelIntegrand y (a + t * I)) (fun t _ => by
      rw [norm_kernelIntegrand hy]
      have hre' : |a| ≤ ‖(a : ℂ) + t * I‖ := by
        simpa using Complex.abs_re_le_norm ((a : ℂ) + t * I)
      have hre : ((a : ℂ) + t * I).re = a := by simp
      rw [hre]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (abs_pos.2 ha) hre')
  have hTT : |T - -T| = 2 * T := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  rw [hTT] at h
  linarith

/-- If `A ≤ B + K / R` for all large `R`, then `A ≤ B`. -/
lemma le_of_forall_le_add_div {A B K R₀ : ℝ} (h : ∀ R, R₀ < R → A ≤ B + K / R) : A ≤ B := by
  have ht : Tendsto (fun R : ℝ => B + K / R) atTop (𝓝 B) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop))
  exact ge_of_tendsto ht ((eventually_gt_atTop R₀).mono h)

/-- The case `0 < y < 1`: the contour is moved to the right. -/
lemma norm_kernel_le_of_lt_one {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    ‖kernel y c T‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hy1
  have habs : |Real.log y| = -Real.log y := abs_of_neg hlog
  refine le_of_forall_le_add_div (R₀ := c) (K := T / Real.pi) fun R hR => ?_
  have hR0 : 0 < R := hc.trans hR
  -- Cauchy's theorem on the rectangle with corners `c - iT` and `R + iT`.
  have hrect : RectangleIntegral (kernelIntegrand y) ⟨c, -T⟩ ⟨R, T⟩ = 0 := by
    refine HolomorphicOn.vanishesOnRectangle (U := {s : ℂ | 0 < s.re}) ?_ ?_
    · intro s hs
      exact (differentiableAt_kernelIntegrand hy
        (fun h => by simp [h] at hs)).differentiableWithinAt
    · intro s hs
      have := hs.1
      simp only [uIcc_of_le hR.le, mem_preimage, mem_Icc] at this
      exact hc.trans_le this.1
  simp only [RectangleIntegral] at hrect
  have hV : VIntegral (kernelIntegrand y) c (-T) T =
      HIntegral (kernelIntegrand y) c R (-T) - HIntegral (kernelIntegrand y) c R T +
        VIntegral (kernelIntegrand y) R (-T) T := by
    linear_combination -hrect
  have hH : ∀ τ : ℝ, |τ| = T →
      ‖HIntegral (kernelIntegrand y) c R τ‖ ≤ y ^ c / (T * |Real.log y|) := by
    intro τ hτ
    refine (norm_hIntegral_le hy hR.le (by rw [← abs_ne_zero, hτ]; exact hT.ne')).trans ?_
    rw [intervalIntegral.integral_div, integral_rpow_base hy hy1.ne, hτ, habs]
    have := Real.rpow_nonneg hy.le R
    have hpos : 0 < T * -Real.log y := mul_pos hT (neg_pos.2 hlog)
    rw [div_div, show Real.log y * T = -(T * -Real.log y) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have hVR : ‖VIntegral (kernelIntegrand y) R (-T) T‖ ≤ 2 * T / R := by
    refine (norm_vIntegral_le hy hR0.ne' hT.le).trans ?_
    rw [abs_of_pos hR0]
    have : y ^ R ≤ 1 := Real.rpow_le_one hy.le hy1.le hR0.le
    have : y ^ R / R ≤ 1 / R := div_le_div_of_nonneg_right this hR0.le
    calc 2 * T * (y ^ R / R) ≤ 2 * T * (1 / R) := by gcongr
      _ = 2 * T / R := by ring
  rw [kernel_eq_vIntegral, norm_mul, norm_pi_I_inv, hV]
  have h1 := hH (-T) (by rw [abs_neg, abs_of_pos hT])
  have h2 := hH T (abs_of_pos hT)
  have htri := norm_add_le (HIntegral (kernelIntegrand y) c R (-T) -
      HIntegral (kernelIntegrand y) c R T) (VIntegral (kernelIntegrand y) R (-T) T)
  have htri2 := norm_sub_le (HIntegral (kernelIntegrand y) c R (-T))
      (HIntegral (kernelIntegrand y) c R T)
  have hpi := Real.pi_pos
  have hsum : ‖HIntegral (kernelIntegrand y) c R (-T) - HIntegral (kernelIntegrand y) c R T +
        VIntegral (kernelIntegrand y) R (-T) T‖ ≤
      2 * (y ^ c / (T * |Real.log y|)) + 2 * T / R := by linarith
  calc (2 * Real.pi)⁻¹ * ‖HIntegral (kernelIntegrand y) c R (-T) -
          HIntegral (kernelIntegrand y) c R T + VIntegral (kernelIntegrand y) R (-T) T‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (y ^ c / (T * |Real.log y|)) + 2 * T / R) := by gcongr
    _ = y ^ c / (Real.pi * T * |Real.log y|) + T / Real.pi / R := by
      field_simp

/-- The case `y > 1`: the contour is moved to the left, past the simple pole at `0`. -/
lemma norm_kernel_sub_one_le_of_one_lt {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖kernel y c T - 1‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  have hy : 0 < y := one_pos.trans hy1
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have habs : |Real.log y| = Real.log y := abs_of_pos hlog
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  refine le_of_forall_le_add_div (R₀ := 0) (K := T / Real.pi) fun R hR0 => ?_
  -- Residue theorem on the rectangle with corners `-R - iT` and `c + iT`.
  have hres : RectangleIntegral' (kernelIntegrand y) ⟨-R, -T⟩ ⟨c, T⟩ = 1 := by
    refine ResidueTheoremOnRectangleWithSimplePole (p := 0) (A := 1)
      (g := dslope (fun s : ℂ => (y : ℂ) ^ s) 0) (by simp; linarith) (by simp; linarith) ?_ ?_ ?_
    · rw [rectangle_mem_nhds_iff]
      simp only [uIoo_of_le (show (-R : ℝ) ≤ c by linarith),
        uIoo_of_le (show (-T : ℝ) ≤ T by linarith)]
      simp [mem_reProdIm, hR0, hc, hT]
    · have hd : DifferentiableOn ℂ (fun s : ℂ => (y : ℂ) ^ s) univ :=
        fun s _ => (differentiableAt_id.const_cpow (Or.inl hy')).differentiableWithinAt
      exact ((differentiableOn_dslope (univ_mem)).2 hd).mono (subset_univ _)
    · intro s hs
      have hs0 : s ≠ 0 := hs.2
      simp only [Pi.sub_apply, kernelIntegrand, sub_zero, dslope_of_ne _ hs0, slope_def_field,
        cpow_zero]
      field_simp
  simp only [RectangleIntegral', RectangleIntegral, smul_eq_mul] at hres
  set H1 := HIntegral (kernelIntegrand y) (-R) c (-T)
  set H2 := HIntegral (kernelIntegrand y) (-R) c T
  set VR := VIntegral (kernelIntegrand y) (-R) (-T) T
  set Vc := VIntegral (kernelIntegrand y) c (-T) T
  have hpiI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hdiff : kernel y c T - 1 = (2 * Real.pi * I)⁻¹ * (VR - H1 + H2) := by
    rw [kernel_eq_vIntegral, ← hres]
    field_simp
    ring
  have hH : ∀ τ : ℝ, |τ| = T →
      ‖HIntegral (kernelIntegrand y) (-R) c τ‖ ≤ y ^ c / (T * |Real.log y|) := by
    intro τ hτ
    refine (norm_hIntegral_le hy (by linarith) (by rw [← abs_ne_zero, hτ]; exact hT.ne')).trans ?_
    rw [intervalIntegral.integral_div, integral_rpow_base hy hy1.ne', hτ, habs]
    have := Real.rpow_nonneg hy.le (-R)
    rw [div_div, mul_comm (Real.log y)]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hVR : ‖VR‖ ≤ 2 * T / R := by
    refine (norm_vIntegral_le hy (by linarith) hT.le).trans ?_
    rw [abs_neg, abs_of_pos hR0]
    have : y ^ (-R) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith)
    have : y ^ (-R) / R ≤ 1 / R := div_le_div_of_nonneg_right this hR0.le
    calc 2 * T * (y ^ (-R) / R) ≤ 2 * T * (1 / R) := by gcongr
      _ = 2 * T / R := by ring
  have h1 := hH (-T) (by rw [abs_neg, abs_of_pos hT])
  have h2 := hH T (abs_of_pos hT)
  have htri := norm_add_le (VR - H1) H2
  have htri2 := norm_sub_le VR H1
  have hsum : ‖VR - H1 + H2‖ ≤ 2 * (y ^ c / (T * |Real.log y|)) + 2 * T / R := by linarith
  have hpi := Real.pi_pos
  rw [hdiff, norm_mul, norm_pi_I_inv]
  calc (2 * Real.pi)⁻¹ * ‖VR - H1 + H2‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (y ^ c / (T * |Real.log y|)) + 2 * T / R) := by gcongr
    _ = y ^ c / (Real.pi * T * |Real.log y|) + T / Real.pi / R := by
      field_simp

/-- **Perron kernel bound.** For `y > 0`, `y ≠ 1`, `c > 0`, `T > 0`,
`|I(y, c, T) - 1_{y > 1}| ≤ y^c / (π T |log y|)`. -/
theorem norm_kernel_sub_indicator_le {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c)
    (hT : 0 < T) :
    ‖kernel y c T - (if 1 < y then 1 else 0)‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  rcases lt_or_gt_of_ne hy1 with h | h
  · rw [if_neg (not_lt.2 h.le), sub_zero]
    exact norm_kernel_le_of_lt_one hy h hc hT
  · rw [if_pos h]
    exact norm_kernel_sub_one_le_of_one_lt h hc hT

/-- `I(1, c, T) = arctan (T / c) / π`. -/
lemma kernel_one {c T : ℝ} (hc : 0 < c) :
    kernel 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
  have h := integral_const_div_re_add_self (A := 1) (y₁ := -T) (y₂ := T) hc.ne'
  simp only [kernel, Complex.ofReal_one, one_cpow, intervalIntegral.integral_mul_const]
  rw [h]
  simp only [neg_sq, sub_self, mul_zero, zero_sub, div_neg, Real.arctan_neg]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp
  ring

lemma norm_kernel_one_le {c T : ℝ} (hc : 0 < c) : ‖kernel 1 c T‖ ≤ 1 / 2 := by
  rw [kernel_one hc, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos,
    div_le_iff₀ Real.pi_pos]
  have h1 := Real.arctan_lt_pi_div_two (T / c)
  have h2 := Real.neg_pi_div_two_lt_arctan (T / c)
  rw [abs_le]
  constructor <;> linarith

/-- Near `y = 1` the kernel is close to `I(1, c, T)`. -/
lemma norm_kernel_sub_kernel_one_le {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hc2 : c ≤ 2)
    (hT : 1 ≤ T) (hlog : |Real.log y| ≤ 1 / (4 * T)) :
    ‖kernel y c T - kernel 1 c T‖ ≤ 1 / 6 := by
  have hT0 : 0 < T := by linarith
  have hs0 : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : ∀ z : ℝ, 0 < z → Continuous fun t : ℝ =>
      (z : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I := fun z hz =>
    (((continuous_cpow_const_base hz).comp (by fun_prop)).div (by fun_prop) hs0).mul
      continuous_const
  have hdiff : kernel y c T - kernel 1 c T = (2 * Real.pi * I)⁻¹ * ∫ t in (-T)..T,
      ((y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I -
        ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I) := by
    rw [kernel, kernel, intervalIntegral.integral_sub ((hcont y hy).intervalIntegrable _ _)
      ((hcont 1 one_pos).intervalIntegrable _ _), mul_sub]
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpt : ∀ t ∈ Ι (-T) T, ‖(y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I -
      ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I‖ ≤ 1 / (2 * T) := by
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    set s : ℂ := (c : ℂ) + t * I
    have hsn : 0 < ‖s‖ := norm_pos_iff.2 (hs0 t)
    have hsle : ‖s‖ ≤ 3 * T := by
      refine (norm_le_abs_re_add_abs_im s).trans ?_
      have hre : s.re = c := by simp [s]
      have him : s.im = t := by simp [s]
      rw [hre, him, abs_of_pos hc]
      have : |t| ≤ T := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
      linarith
    have hw : ‖(Real.log y : ℂ) * s‖ = |Real.log y| * ‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hw1 : ‖(Real.log y : ℂ) * s‖ ≤ 1 := by
      rw [hw]
      calc |Real.log y| * ‖s‖ ≤ 1 / (4 * T) * (3 * T) := by gcongr
        _ ≤ 1 := by field_simp; linarith
    have hexp := norm_exp_sub_one_le hw1
    have heq : (y : ℂ) ^ s / s * I - ((1 : ℝ) : ℂ) ^ s / s * I =
        (exp ((Real.log y : ℂ) * s) - 1) / s * I := by
      rw [cpow_def_of_ne_zero hy', ← Complex.ofReal_log hy.le, Complex.ofReal_one, one_cpow]
      ring
    rw [heq, norm_mul, norm_I, mul_one, norm_div, div_le_iff₀ hsn]
    calc ‖exp ((Real.log y : ℂ) * s) - 1‖ ≤ 2 * (|Real.log y| * ‖s‖) := by rw [← hw]; exact hexp
      _ ≤ 2 * (1 / (4 * T) * ‖s‖) := by gcongr
      _ = 1 / (2 * T) * ‖s‖ := by field_simp; ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hTT : |T - -T| = 2 * T := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  rw [hTT, show 1 / (2 * T) * (2 * T) = 1 by field_simp] at hint
  rw [hdiff, norm_mul, norm_pi_I_inv]
  have hpi := Real.pi_gt_three
  calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, ((y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I -
        ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) * I)‖
      ≤ (2 * Real.pi)⁻¹ * 1 := by gcongr
    _ ≤ 1 / 6 := by
      rw [mul_one, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith

/-- **Uniform Perron kernel bound.** For `0 < c ≤ 2`, `T ≥ 1` and every `y > 0`,
`|I(y, c, T) - 1_{y > 1}| ≤ 4 y^c`. -/
theorem norm_kernel_sub_indicator_le_four {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hc2 : c ≤ 2)
    (hT : 1 ≤ T) :
    ‖kernel y c T - (if 1 < y then 1 else 0)‖ ≤ 4 * y ^ c := by
  have hT0 : 0 < T := by linarith
  by_cases hsmall : |Real.log y| ≤ 1 / (4 * T)
  · have hyc : 1 / 2 ≤ y ^ c := by
      rw [Real.rpow_def_of_pos hy]
      have h1 : |Real.log y * c| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hc]
        calc |Real.log y| * c ≤ 1 / (4 * T) * 2 := by gcongr
          _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
                          linarith
      linarith [neg_abs_le (Real.log y * c), Real.add_one_le_exp (Real.log y * c)]
    have h1 := norm_kernel_sub_kernel_one_le hy hc hc2 hT hsmall
    have h2 := norm_kernel_one_le (T := T) hc
    have h3 : ‖(if 1 < y then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc ‖kernel y c T - (if 1 < y then 1 else 0)‖
        = ‖(kernel y c T - kernel 1 c T) + kernel 1 c T - (if 1 < y then 1 else 0)‖ := by
          ring_nf
      _ ≤ ‖kernel y c T - kernel 1 c T‖ + ‖kernel 1 c T‖ + ‖(if 1 < y then (1 : ℂ) else 0)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ 4 * y ^ c := by linarith
  · push_neg at hsmall
    have hy1 : y ≠ 1 := by
      rintro rfl
      simp only [Real.log_one, abs_zero] at hsmall
      have : 0 < 1 / (4 * T) := by positivity
      linarith
    refine (norm_kernel_sub_indicator_le hy hy1 hc hT0).trans ?_
    have hq : 1 / 4 < T * |Real.log y| := by
      rw [div_lt_iff₀ (by positivity)] at hsmall
      linarith
    have hyc := Real.rpow_nonneg hy.le c
    have hpi := Real.pi_gt_three
    rw [div_le_iff₀ (by rw [mul_assoc]; exact mul_pos Real.pi_pos (by linarith))]
    nlinarith [mul_le_mul_of_nonneg_left hq.le hyc]

end Cubic.Analysis.Perron
