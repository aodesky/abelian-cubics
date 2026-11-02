import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Mellin transforms of continuous functions supported in a compact subinterval
of the positive real axis. These facts use the actual integral and mathlib's
Mellin calculus; no analytic hypothesis is introduced. -/

noncomputable section

namespace Cubic.Analysis.CompactMellin

open Set Filter Asymptotics MeasureTheory Complex
open scoped Topology

variable {f : ℝ → ℂ} {a b : ℝ}

theorem zero_outside (hs : Function.support f ⊆ Icc a b) {x : ℝ}
    (hx : x ∉ Icc a b) : f x = 0 := by
  by_contra hn
  exact hx (hs hn)

theorem zero_atTop (hs : Function.support f ⊆ Icc a b) :
    f =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop b] with x hx
  exact zero_outside hs (fun h => not_lt_of_ge h.2 hx)

theorem zero_near_zero (ha : 0 < a) (hs : Function.support f ⊆ Icc a b) :
    f =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (gt_mem_nhds ha)] with x _ hx
  exact zero_outside hs (fun h => not_lt_of_ge h.1 hx)

theorem convergent (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) (s : ℂ) : MellinConvergent f s := by
  apply mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1) (hf.locallyIntegrable.locallyIntegrableOn _)
  · exact (zero_atTop hs).trans_isBigO (isBigO_zero _ _)
  · linarith
  · exact (zero_near_zero ha hs).trans_isBigO (isBigO_zero _ _)
  · linarith

theorem hasDerivAt (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) (s : ℂ) :
    HasDerivAt (mellin f) (mellin (fun x => Real.log x • f x) s) s := by
  apply (mellin_hasDerivAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1) (hf.locallyIntegrable.locallyIntegrableOn _)
    ((zero_atTop hs).trans_isBigO (isBigO_zero _ _)) (by linarith)
    ((zero_near_zero ha hs).trans_isBigO (isBigO_zero _ _)) (by linarith)).2

theorem entire (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) : Differentiable ℂ (mellin f) :=
  fun s => (hasDerivAt hf ha hs s).differentiableAt

theorem log_convergent (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) (s : ℂ) :
    MellinConvergent (fun x => Real.log x • f x) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1) (hf.locallyIntegrable.locallyIntegrableOn _)
    ((zero_atTop hs).trans_isBigO (isBigO_zero _ _)) (by linarith)
    ((zero_near_zero ha hs).trans_isBigO (isBigO_zero _ _)) (by linarith)).1

theorem at_one (f : ℝ → ℂ) : mellin f 1 = ∫ x in Ioi (0 : ℝ), f x := by
  simp [mellin]

theorem integrable (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) : IntegrableOn f (Ioi 0) := by
  simpa [MellinConvergent] using convergent hf ha hs 1

theorem log_integrable (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) :
    IntegrableOn (fun x => (Real.log x : ℂ) * f x) (Ioi 0) := by
  simpa [MellinConvergent, Complex.real_smul] using log_convergent hf ha hs 1

theorem inversion (hf : Continuous f) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) (σ : ℝ)
    (hvert : VerticalIntegrable (mellin f) σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin f) x = f x :=
  mellinInv_mellin_eq σ f hx (convergent hf ha hs σ) hvert hf.continuousAt

end Cubic.Analysis.CompactMellin
