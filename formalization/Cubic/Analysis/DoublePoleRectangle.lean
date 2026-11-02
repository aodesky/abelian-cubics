import Cubic.PoissonSummation.RectangleResidue
import Cubic.PoissonSummation.AnalyticLaurent
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The residue of a double pole in a Perron rectangle

An analytic step in the proof of `eqn:dSummatoryForGeneralTrace`: if `f` has the
Laurent expansion `A (s - 1)⁻² + B (s - 1)⁻¹ + O(1)` at `s = 1`, the
counterclockwise rectangle integral of `f(s) X^s / s` around `1` equals
`2πi (A X log X + (B - A) X)`, the residue at `s = 1`.

The proof removes the singular part of `f(s) X^s / s` at `1`: the double pole
term `A X (s - 1)⁻²` has the primitive `-A X (s - 1)⁻¹`, so it integrates to
zero, and the remaining simple pole has residue `A φ'(1) + B φ(1)` for
`φ(s) = X^s / s`.
-/

noncomputable section

namespace Cubic.Analysis.DoublePoleRectangle

open Complex Filter Asymptotics Set MeasureTheory intervalIntegral
open scoped Topology Interval
open Cubic.PoissonSummation.RectangleResidue

/-- The four sides of the rectangle integral with corners `β - iT` and `c + iT`. -/
theorem rectangleIntegral_eq (g : ℂ → ℂ) (β c T : ℝ) :
    RectangleIntegral g ((β : ℂ) - T * I) ((c : ℂ) + T * I) =
      (∫ x in β..c, g (x + (-T) * I)) - (∫ x in β..c, g (x + T * I)) +
        I * (∫ t in (-T)..T, g (c + t * I)) - I * (∫ t in (-T)..T, g (β + t * I)) := by
  simp [RectangleIntegral, HIntegral, VIntegral]

/-- A rectangle integral of a derivative vanishes when the primitive is
differentiable on the border. -/
theorem rectangleIntegral_deriv_eq_zero {F F' : ℂ → ℂ} {z w : ℂ}
    (hF : ∀ s ∈ RectangleBorder z w, HasDerivAt F (F' s) s)
    (hc : ContinuousOn F' (RectangleBorder z w)) :
    RectangleIntegral F' z w = 0 := by
  have hint := hc.rectangleBorder_integrable
  have hH : ∀ y : ℝ, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + y * I ∈ RectangleBorder z w) →
      IntervalIntegrable (fun x : ℝ => F' (x + y * I)) volume z.re w.re →
      HIntegral F' z.re w.re y = F (w.re + y * I) - F (z.re + y * I) := by
    intro y hy hi
    rw [HIntegral]
    refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + y * I)) (fun x hx => ?_) hi
    have h1 : HasDerivAt (fun u : ℂ => F (u + y * I)) (F' (x + y * I)) (x : ℂ) :=
      by simpa using (hF _ (hy x hx)).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))
    exact h1.comp_ofReal
  have hV : ∀ x : ℝ, (∀ y ∈ [[z.im, w.im]], (x : ℂ) + y * I ∈ RectangleBorder z w) →
      IntervalIntegrable (fun y : ℝ => F' (x + y * I)) volume z.im w.im →
      VIntegral F' x z.im w.im = F (x + w.im * I) - F (x + z.im * I) := by
    intro x hx hi
    rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => F (x + t * I)) (fun y hy => ?_)
      (hi.const_mul I)
    have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    have h2 := (hF _ (hx y hy)).comp y h1
    simpa [mul_comm] using h2
  rw [RectangleIntegral,
    hH z.im (fun x hx => mapsTo_rectangleBorder_left_im z w hx) hint.1,
    hH w.im (fun x hx => mapsTo_rectangleBorder_right_im z w hx) hint.2.1,
    hV w.re (fun y hy => mapsTo_rectangleBorder_right_re z w hy) hint.2.2.1,
    hV z.re (fun y hy => mapsTo_rectangleBorder_left_re z w hy) hint.2.2.2]
  ring

/-- The rectangle integral of a pure double pole vanishes: `K (s - p)⁻²` has the
primitive `-K (s - p)⁻¹` off `p`. -/
theorem rectangleIntegral_double_pole_eq_zero {z w p : ℂ} (K : ℂ)
    (hp : p ∉ RectangleBorder z w) :
    RectangleIntegral (fun s => K / (s - p) ^ 2) z w = 0 := by
  have hne : ∀ s ∈ RectangleBorder z w, s - p ≠ 0 := fun s hs h =>
    hp (by rwa [sub_eq_zero.mp h] at hs)
  refine rectangleIntegral_deriv_eq_zero (F := fun s => -K * (s - p)⁻¹) (fun s hs => ?_) ?_
  · have h := (((hasDerivAt_id s).sub_const p).inv (hne s hs)).const_mul (-K)
    convert h using 1
    simp only [id]
    ring
  · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (hne s hs))

/-- `X^s / s` at `s = 1`: value `X` and derivative `X log X - X`. -/
theorem hasDerivAt_cpow_div (X : ℝ) (hX : 0 < X) :
    HasDerivAt (fun s : ℂ => (X : ℂ) ^ s / s)
      ((X : ℂ) * Real.log X - X) 1 := by
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have h := ((hasDerivAt_id (1 : ℂ)).const_cpow (c := (X : ℂ)) (Or.inl hX0)).div
    (hasDerivAt_id (1 : ℂ)) one_ne_zero
  convert h using 1
  simp [ofReal_log hX.le]

theorem rectangle_double_pole {f : ℂ → ℂ} {β c T X : ℝ} {A B : ℂ}
    (hβ0 : 0 < β) (hβ : β < 1) (hc : 1 < c) (hT : 0 < T) (hX : 0 < X)
    {U : Set ℂ} (hU : IsOpen U)
    (hR : Rectangle ((β : ℂ) - T * I) ((c : ℂ) + T * I) ⊆ U)
    (hf : DifferentiableOn ℂ f (U \ {1}))
    (hL : (fun s => f s - A / (s - 1) ^ 2 - B / (s - 1)) =O[𝓝[≠] (1 : ℂ)]
      (fun _ => (1 : ℂ))) :
    RectangleIntegral (fun s => f s * (X : ℂ) ^ s / s) ((β : ℂ) - T * I) ((c : ℂ) + T * I) =
      2 * Real.pi * I * (A * X * Real.log X + (B - A) * X) := by
  set z : ℂ := (β : ℂ) - T * I with hz
  set w : ℂ := (c : ℂ) + T * I with hw
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  -- the kernel `φ(s) = X^s / s` and its Taylor data at `1`
  set φ : ℂ → ℂ := fun s => (X : ℂ) ^ s / s with hφ
  set a1 : ℂ := (X : ℂ) * Real.log X - X with ha1
  have hφ1 : φ 1 = X := by simp [hφ]
  have hφd : DifferentiableOn ℂ φ {s | s ≠ 0} := fun s hs =>
    (((differentiableAt_id).const_cpow (Or.inl hX0)).div differentiableAt_id hs).differentiableWithinAt
  have hopen0 : IsOpen {s : ℂ | s ≠ 0} := isOpen_ne
  have hφa : AnalyticAt ℂ φ 1 :=
    hφd.analyticAt (hopen0.mem_nhds (by simp))
  have hderiv : deriv φ 1 = a1 := (hasDerivAt_cpow_div X hX).deriv
  obtain ⟨Rφ, hRφ, hRe⟩ := Cubic.PoissonSummation.AnalyticLaurent.quadratic_remainder hφa
  rw [hderiv, hφ1] at hRe
  -- the rectangle, the open set `U'`, and the position of `1`
  set U' : Set ℂ := U ∩ {s | 0 < s.re} with hU'
  have hU'o : IsOpen U' := hU.inter (isOpen_lt continuous_const continuous_re)
  have hzre : z.re = β := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = c := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hRU' : Rectangle z w ⊆ U' := by
    intro s hs
    refine ⟨hR hs, ?_⟩
    have h1 : s.re ∈ [[z.re, w.re]] := hs.1
    rw [hzre, hwre, uIcc_of_le (by linarith)] at h1
    exact lt_of_lt_of_le hβ0 h1.1
  have h1mem : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, hzre, hwre, hzim, hwim, uIoo_of_le (by linarith),
      uIoo_of_le (by linarith)]
    exact ⟨⟨by simpa using hβ, by simpa using hc⟩, ⟨by simpa using hT, by simpa using hT⟩⟩
  have h1U' : U' ∈ 𝓝 (1 : ℂ) := Filter.mem_of_superset h1mem hRU'
  have h1border : (1 : ℂ) ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_rectangle_mem_nhds h1mem
  -- the regular part `G`
  set C : ℂ := A * a1 + B * X with hC
  set G : ℂ → ℂ := fun s => f s * φ s - A * X / (s - 1) ^ 2 - C / (s - 1) with hG
  have hU'φ : U' \ {1} ⊆ {s : ℂ | s ≠ 0} := fun s hs h0 => by
    have := hs.1.2
    rw [show s = 0 from h0] at this
    simp at this
  have hGd : DifferentiableOn ℂ G (U' \ {1}) := by
    have hs1 : ∀ s ∈ U' \ {1}, s - 1 ≠ 0 := fun s hs h => hs.2 (sub_eq_zero.mp h)
    refine ((((hf.mono fun s hs => ⟨hs.1.1, hs.2⟩).mul (hφd.mono hU'φ)).sub
      (differentiableOn_const _ |>.div ((differentiableOn_id.sub_const 1).pow 2)
        fun s hs => pow_ne_zero 2 (hs1 s hs))).sub
      (differentiableOn_const _ |>.div (differentiableOn_id.sub_const 1) hs1))
  -- `G` is bounded near `1`
  set h : ℂ → ℂ := fun s => f s - A / (s - 1) ^ 2 - B / (s - 1) with hh
  have hGeq : G =ᶠ[𝓝[≠] (1 : ℂ)] fun s => h s * φ s + A * Rφ s + B * (a1 + (s - 1) * Rφ s) := by
    filter_upwards [nhdsWithin_le_nhds hRe, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [hG, hh]
    rw [hs]
    field_simp
    ring
  have hRφb : Rφ =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) :=
    (hRφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hφb : φ =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) :=
    (hφa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hlin : (fun s : ℂ => s - 1) =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    exact (this.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hGb : G =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
    refine IsBigO.congr' ?_ hGeq.symm EventuallyEq.rfl
    have e1 : (fun s => h s * φ s) =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
      simpa using hL.mul hφb
    have e2 : (fun s => A * Rφ s) =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := hRφb.const_mul_left A
    have e3 : (fun s => B * (a1 + (s - 1) * Rφ s)) =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
      refine IsBigO.const_mul_left ?_ B
      exact (isBigO_const_const a1 one_ne_zero _).add (by simpa using hlin.mul hRφb)
    exact (e1.add e2).add e3
  -- removable singularity
  set g : ℂ → ℂ := Function.update G 1 (limUnder (𝓝[≠] (1 : ℂ)) G) with hg
  have hgd : DifferentiableOn ℂ g U' := by
    refine differentiableOn_update_limUnder_of_isLittleO h1U' hGd ?_
    refine Filter.IsBoundedUnder.isLittleO_sub_self_inv ?_
    have : (fun s => G s - G 1) =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) :=
      hGb.sub (isBigO_const_const _ one_ne_zero _)
    exact (isBigO_one_iff ℂ).mp this
  -- the simple-pole residue theorem for `F = f φ - A X (s - 1)⁻²`
  set F : ℂ → ℂ := fun s => f s * φ s - A * X / (s - 1) ^ 2 with hF
  have hres : RectangleIntegral' F z w = C := by
    refine ResidueTheoremOnRectangleWithSimplePole (g := g)
      (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) h1mem
      (hgd.mono hRU') ?_
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    simp [hg, Function.update_of_ne hs1, hG, hF]
  have hresF : RectangleIntegral F z w = 2 * Real.pi * I * C := by
    rw [RectangleIntegral'] at hres
    have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [← hres, smul_eq_mul, ← mul_assoc, mul_one_div_cancel h2, one_mul]
  -- the double pole integrates to zero
  have hdouble : RectangleIntegral (fun s => A * X / (s - 1) ^ 2) z w = 0 :=
    rectangleIntegral_double_pole_eq_zero _ h1border
  -- integrability on the border
  have hsub : Rectangle z w \ {1} ⊆ U' \ {1} := fun s hs => ⟨hRU' hs.1, hs.2⟩
  have hFi : RectangleBorderIntegrable F z w := by
    refine ContinuousOn.rectangleBorderNoPIntegrable ?_ h1border
    have hs1 : ∀ s ∈ Rectangle z w \ {1}, (s - 1) ^ 2 ≠ 0 := fun s hs =>
      pow_ne_zero 2 (sub_ne_zero.mpr hs.2)
    exact (((hf.mono fun s hs => ⟨hs.1.1, hs.2⟩).mul (hφd.mono hU'φ)).mono hsub).continuousOn.sub
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2) hs1)
  have hDi : RectangleBorderIntegrable (fun s => A * X / (s - 1) ^ 2) z w := by
    refine ContinuousOn.rectangleBorderNoPIntegrable ?_ h1border
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr hs.2)
  have hsplit : (fun s => f s * (X : ℂ) ^ s / s) = F + fun s => A * X / (s - 1) ^ 2 := by
    funext s
    simp [hF, hφ, mul_div_assoc]
  rw [hsplit, hFi.add hDi, hresF, hdouble, add_zero, hC, ha1]
  ring

end Cubic.Analysis.DoublePoleRectangle
