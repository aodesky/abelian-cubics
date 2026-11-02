import Cubic.Analysis.DoublePoleRectangle
import Cubic.Analysis.MellinDirichletPairing
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Passing from finite rectangle identities to the absolutely convergent
integrals on two infinite vertical lines. The horizontal sides are explicit;
their disappearance is proved from a uniform strip bound. -/

noncomputable section

namespace Cubic.Analysis.VerticalContourShift

open Complex MeasureTheory Filter Set Asymptotics
open Cubic.PoissonSummation.RectangleResidue
open Cubic.Analysis.DoublePoleRectangle
open Cubic.Analysis.MellinDirichletPairing
open scoped Topology Interval

/-- A Laurent expansion through its simple-pole coefficient determines the
rectangle integral. The bounded remainder is made holomorphic by the removable
singularity theorem; the pure double pole has an explicit primitive. -/
theorem rectangle_of_laurent {f : ℂ → ℂ} {β c T : ℝ} {A B : ℂ}
    (hβ : β < 1) (hc : 1 < c) (hT : 0 < T)
    {U : Set ℂ}
    (hR : Rectangle ((β : ℂ) - T * I) ((c : ℂ) + T * I) ⊆ U)
    (hf : DifferentiableOn ℂ f (U \ {1}))
    (hL : (fun s => f s - A / (s - 1) ^ 2 - B / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ))) :
    RectangleIntegral f ((β : ℂ) - T * I) ((c : ℂ) + T * I) =
      2 * Real.pi * I * B := by
  set z : ℂ := (β : ℂ) - T * I with hz
  set v : ℂ := (c : ℂ) + T * I with hv
  have hzre : z.re = β := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hvre : v.re = c := by simp [hv]
  have hvim : v.im = T := by simp [hv]
  have h1mem : Rectangle z v ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, hzre, hvre, hzim, hvim,
      uIoo_of_le (by linarith), uIoo_of_le (by linarith)]
    exact ⟨⟨by simpa using hβ, by simpa using hc⟩,
      ⟨by simpa using hT, by simpa using hT⟩⟩
  have h1U : U ∈ 𝓝 (1 : ℂ) := Filter.mem_of_superset h1mem hR
  have h1border : (1 : ℂ) ∉ RectangleBorder z v :=
    not_mem_rectangleBorder_of_rectangle_mem_nhds h1mem
  let G : ℂ → ℂ := fun s => f s - A / (s - 1) ^ 2 - B / (s - 1)
  have hne : ∀ s ∈ U \ {(1 : ℂ)}, s - 1 ≠ 0 :=
    fun s hs => sub_ne_zero.mpr hs.2
  have hGd : DifferentiableOn ℂ G (U \ {1}) :=
    (hf.sub ((differentiableOn_const _).div
      ((differentiableOn_id.sub_const 1).pow 2) (fun s hs => pow_ne_zero 2 (hne s hs)))).sub
      ((differentiableOn_const _).div (differentiableOn_id.sub_const 1) hne)
  let g : ℂ → ℂ := Function.update G 1 (limUnder (𝓝[≠] (1 : ℂ)) G)
  have hgd : DifferentiableOn ℂ g U := by
    refine differentiableOn_update_limUnder_of_isLittleO h1U hGd ?_
    apply Filter.IsBoundedUnder.isLittleO_sub_self_inv
    exact (isBigO_one_iff ℂ).mp
      (hL.sub (isBigO_const_const (G 1) one_ne_zero _))
  let F : ℂ → ℂ := fun s => f s - A / (s - 1) ^ 2
  have hres : RectangleIntegral' F z v = B := by
    refine ResidueTheoremOnRectangleWithSimplePole (g := g)
      (by rw [hzre, hvre]; linarith) (by rw [hzim, hvim]; linarith) h1mem
      (hgd.mono hR) ?_
    intro s hs
    simp [g, Function.update_of_ne hs.2, G, F]
  have hresF : RectangleIntegral F z v = 2 * Real.pi * I * B := by
    rw [RectangleIntegral'] at hres
    have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [← hres, smul_eq_mul, ← mul_assoc, mul_one_div_cancel h2, one_mul]
  have hsub : Rectangle z v \ {1} ⊆ U \ {1} := fun s hs => ⟨hR hs.1, hs.2⟩
  have hFi : RectangleBorderIntegrable F z v := by
    apply ContinuousOn.rectangleBorderNoPIntegrable _ h1border
    exact ((hf.mono hsub).continuousOn.sub
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr hs.2))))
  have hDi : RectangleBorderIntegrable (fun s => A / (s - 1) ^ 2) z v := by
    apply ContinuousOn.rectangleBorderNoPIntegrable _ h1border
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr hs.2))
  have he : f = F + (fun s => A / (s - 1) ^ 2) := by
    funext s
    simp [F]
  rw [he, hFi.add hDi, hresF, rectangleIntegral_double_pole_eq_zero _ h1border, add_zero]

theorem shift_of_rectangles {f : ℂ → ℂ} {β c : ℝ} {R : ℂ}
    (hβ : VerticalIntegrable f β) (hc : VerticalIntegrable f c)
    (hminus : Tendsto (fun T : ℝ => ∫ x in β..c, f (x + (-T) * I)) atTop (𝓝 0))
    (hplus : Tendsto (fun T : ℝ => ∫ x in β..c, f (x + T * I)) atTop (𝓝 0))
    (hrect : ∀ T : ℝ, 0 < T →
      RectangleIntegral f ((β : ℂ) - T * I) ((c : ℂ) + T * I) =
        2 * Real.pi * I * R) :
    (∫ t : ℝ, f (c + t * I)) = 2 * Real.pi * R + ∫ t : ℝ, f (β + t * I) := by
  have hvc := intervalIntegral_tendsto_integral hc
    tendsto_neg_atTop_atBot tendsto_id
  have hvβ := intervalIntegral_tendsto_integral hβ
    tendsto_neg_atTop_atBot tendsto_id
  have hh := ((hminus.sub hplus).add (hvc.const_mul I)).sub (hvβ.const_mul I)
  have hr : Tendsto (fun T : ℝ =>
      (∫ x in β..c, f (x + (-T) * I)) - (∫ x in β..c, f (x + T * I)) +
        I * (∫ t in (-T)..T, f (c + t * I)) - I * (∫ t in (-T)..T, f (β + t * I)))
      atTop (𝓝 (2 * Real.pi * I * R)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact ((rectangleIntegral_eq f β c T).symm.trans (hrect T hT)).symm
  have he := tendsto_nhds_unique hh hr
  simp only [sub_self, zero_add] at he
  have he' : I * ((∫ t : ℝ, f (c + t * I)) - ∫ t : ℝ, f (β + t * I)) =
      I * (2 * Real.pi * R) := by linear_combination he
  have hd := mul_left_cancel₀ I_ne_zero he'
  linear_combination hd

theorem horizontal_vanishes {f : ℂ → ℂ} {β c C : ℝ}
    (hβc : β ≤ c)
    (hb : ∀ x ∈ Icc β c, ∀ t : ℝ, 1 ≤ |t| → ‖f (x + t * I)‖ ≤ C / (1 + |t|) ^ 2)
    (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x in β..c, f (x + (ε * T) * I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (C * (c - β)) * ((1 + T)⁻¹) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)).pow 2
    simpa using h.const_mul (C * (c - β))
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have heT : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := β) (b := c) (f := fun x : ℝ => f (x + (ε * T) * I))
    (C := C / (1 + T) ^ 2) (fun x hx => by
      rw [uIoc_of_le hβc] at hx
      simpa only [heT, Complex.ofReal_mul] using
        hb x ⟨hx.1.le, hx.2⟩ (ε * T) (by simpa only [heT] using hT))
  rw [abs_of_nonneg (sub_nonneg.mpr hβc)] at hi
  convert hi using 1
  rw [div_eq_mul_inv, inv_pow]
  ring

theorem normalized_shift {F H : ℂ → ℂ} {β c : ℝ} {R : ℂ}
    (h : (∫ t : ℝ, F (c + t * I) * H (c + t * I)) =
      2 * Real.pi * R + ∫ t : ℝ, F (β + t * I) * H (β + t * I)) :
    pairing c F H = R + pairing β F H := by
  simp only [pairing, Complex.real_smul]
  rw [h]
  push_cast
  field_simp
  simp only [mul_comm I]

end Cubic.Analysis.VerticalContourShift
