import Cubic.BoxAsymptotic.SmoothArcGeometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Wrapped profiles supported strictly away from the representative seam
are smooth. The proof checks both the affine local charts and the zero
neighborhood of the seam; it never differentiates the discontinuous wrap
function there. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothWrappedProfile

open Set Filter
open CubicTargets.BoxAsymptotic
open scoped Topology ContDiff

def profile (Ψ : ℝ → ℝ) (Θ t : ℝ) : ℝ := Ψ (wrap t / Θ)

theorem wrap_locally_affine {x : ℝ} (hx : wrap x < Real.pi) :
    ∃ c : ℝ, wrap =ᶠ[𝓝 x] (fun y => y - c) := by
  let c := toIocDiv Real.two_pi_pos (-Real.pi) x • (2 * Real.pi)
  have he : wrap x = x - c := rfl
  have hl : -Real.pi < x - c := by
    rw [← he]
    exact (toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) x).1
  have hh : x - c < Real.pi := by rwa [← he]
  have hnear : ∀ᶠ y in 𝓝 x, y - c ∈ Ioo (-Real.pi) Real.pi :=
    (continuous_id.sub continuous_const).continuousAt
      (isOpen_Ioo.mem_nhds ⟨hl, hh⟩)
  refine ⟨c, ?_⟩
  filter_upwards [hnear] with y hy
  apply (toIocMod_eq_iff Real.two_pi_pos).mpr
  refine ⟨⟨hy.1, by linarith [hy.2]⟩, toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  dsimp [c]
  abel

theorem deriv_support {Ψ : ℝ → ℝ} (hs : Function.support Ψ ⊆ Icc (-4) 4) :
    Function.support (deriv Ψ) ⊆ Icc (-4) 4 :=
  support_deriv_subset.trans (closure_minimal hs isClosed_Icc)

theorem profile_zero {Ψ : ℝ → ℝ} {Θ t : ℝ}
    (hs : Function.support Ψ ⊆ Icc (-4) 4) (hΘ : 0 < Θ)
    (ht : 4 * Θ < |wrap t|) : profile Ψ Θ t = 0 := by
  by_contra hn
  have h := hs hn
  have hab : |wrap t / Θ| ≤ 4 := abs_le.mpr ⟨h.1, h.2⟩
  rw [abs_div, abs_of_pos hΘ, div_le_iff₀ hΘ] at hab
  linarith

theorem near_zero {Ψ : ℝ → ℝ} {Θ x : ℝ}
    (hs : Function.support Ψ ⊆ Icc (-4) 4) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4)
    (hx : Real.pi ≤ wrap x) : profile Ψ Θ =ᶠ[𝓝 x] (fun _ => 0) := by
  have hh : 4 * Θ < |wrap x| := by
    have := Real.pi_gt_three
    have := le_abs_self (wrap x)
    linarith
  have hnear : ∀ᶠ y in 𝓝 x, 4 * Θ < |wrap y| :=
    SmoothArcGeometry.continuous_abs_wrap.continuousAt (Ioi_mem_nhds hh)
  filter_upwards [hnear] with y hy
  exact profile_zero hs hΘ hy

theorem smooth {Ψ : ℝ → ℝ} {Θ : ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Icc (-4) 4) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    ContDiff ℝ ∞ (profile Ψ Θ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : wrap x < Real.pi
  · obtain ⟨c, hc⟩ := wrap_locally_affine hx
    have hcSmooth : ContDiff ℝ ∞ (fun y : ℝ => (y - c) / Θ) :=
      (contDiff_id.sub contDiff_const).div_const Θ
    apply (hΨ.comp hcSmooth).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hc] with y hy
    simp only [profile, hy, Function.comp_apply]
  · exact contDiffAt_const.congr_of_eventuallyEq (near_zero hs hΘ hΘ' (le_of_not_gt hx))

theorem hasDerivAt {Ψ : ℝ → ℝ} {Θ : ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Icc (-4) 4) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) (x : ℝ) :
    HasDerivAt (profile Ψ Θ) (profile (deriv Ψ) Θ x / Θ) x := by
  by_cases hx : wrap x < Real.pi
  · obtain ⟨c, hc⟩ := wrap_locally_affine hx
    have hd := ((hΨ.differentiable (by simp)) ((x - c) / Θ)).hasDerivAt.comp x
      (((hasDerivAt_id x).sub_const c).div_const Θ)
    have he : wrap x = x - c := hc.self_of_nhds
    have heq : profile Ψ Θ =ᶠ[𝓝 x] (fun y => Ψ ((y - c) / Θ)) := by
      filter_upwards [hc] with y hy
      simp only [profile, hy]
    convert hd.congr_of_eventuallyEq heq using 1
    simp only [profile, he]
    ring
  · have hh : 4 * Θ < |wrap x| := by
      have := Real.pi_gt_three
      have := le_abs_self (wrap x)
      have := le_of_not_gt hx
      linarith
    rw [profile_zero (deriv_support hs) hΘ hh, zero_div]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (near_zero hs hΘ hΘ' (le_of_not_gt hx))

theorem periodic (Ψ : ℝ → ℝ) (Θ t : ℝ) :
    profile Ψ Θ (t + 2 * Real.pi) = profile Ψ Θ t := by
  simp only [profile, wrap, toIocMod_add_right]

end Cubic.BoxAsymptotic.SmoothWrappedProfile
