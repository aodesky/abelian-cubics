import Cubic.BoxAsymptotic.AngularMomentData
import Cubic.BoxAsymptotic.AngularSeriesConvergence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Convex.Topology

/-! Uniqueness and Fourier symmetries of analytic realizations.  The symmetries
are proved from the original series by the identity theorem, including the
conjugation of the vertical parameter.  Existence is not assumed here. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularContinuation

open Cubic.BoxAsymptotic.AngularMomentData
open scoped Topology

theorem halfPlane_eq {a : ℝ} (ha : a < 1) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | a < s.re})
    (hg : DifferentiableOn ℂ g {s | a < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → f s = g s) :
    Set.EqOn f g {s : ℂ | a < s.re} := by
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | a < s.re} :=
    (convex_halfSpace_gt Complex.reLm.isLinear a).isPreconnected
  have hn : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  apply (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hopen) hconn (z₀ := (2 : ℂ)) (by norm_num; linarith)
  exact Filter.mem_of_superset hn (fun s hs => heq s hs)

theorem conjugate_holomorphic {a : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | a < s.re}) :
    DifferentiableOn ℂ (fun s => star (f (star s))) {s : ℂ | a < s.re} := by
  intro s hs
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs' : star s ∈ {s : ℂ | a < s.re} := by simpa using hs
  have h := (hf.differentiableAt (hopen.mem_nhds hs')).conj_conj
  have h' : DifferentiableAt ℂ (fun s => star (f (star s))) s := by
    simpa only [Function.comp_def, starRingEnd_apply, star_star] using h
  exact h'.differentiableWithinAt

theorem odd_zero {L F : ℤ → ℂ → ℂ} (h : AnalyticRealization L F)
    {k : ℤ} (hk : Odd k) {s : ℂ} (hs : 1 / 2 < s.re) : F k s = 0 := by
  have hk0 : k ≠ 0 := by intro he; simpa [he] using hk
  apply halfPlane_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (h.angular_holomorphic k hk0) (differentiableOn_const 0) ?_ hs
  intro z hz
  rw [h.angular_eq k hk0 z hz, AngularSeriesConvergence.series_odd hk]

theorem neg_index {L F : ℤ → ℂ → ℂ} (h : AnalyticRealization L F)
    {k : ℤ} (hk : k ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    F (-k) s = star (F k (star s)) := by
  apply halfPlane_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (h.angular_holomorphic (-k) (neg_ne_zero.mpr hk))
    (conjugate_holomorphic (h.angular_holomorphic k hk)) ?_ hs
  intro z hz
  rw [h.angular_eq (-k) (neg_ne_zero.mpr hk) z hz,
    h.angular_eq k hk (star z) (by simpa using hz), AngularSeriesConvergence.series_neg]

theorem angular_unique {L F L' F' : ℤ → ℂ → ℂ}
    (h : AnalyticRealization L F) (h' : AnalyticRealization L' F')
    {k : ℤ} (hk : k ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) : F k s = F' k s := by
  apply halfPlane_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (h.angular_holomorphic k hk) (h'.angular_holomorphic k hk) ?_ hs
  intro z hz
  rw [h.angular_eq k hk z hz, h'.angular_eq k hk z hz]

end Cubic.BoxAsymptotic.AngularContinuation
