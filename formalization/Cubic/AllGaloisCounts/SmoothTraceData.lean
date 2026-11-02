import Cubic.AllGaloisCounts.SlicePrimitive
import Cubic.AllGaloisCounts.TrapezoidalGrid
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Smooth functions on a neighborhood of the trace interval have uniform
first- and second-derivative bounds. The actual slice integral has such an
extension, supplied by its moving-endpoint formula. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SmoothTraceData
open MeasureTheory

def domain : Set ℝ := Set.Ioo (-2) 2
def interval : Set ℝ := Set.Icc (-1) 1

theorem subset : interval ⊆ domain := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

variable {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f domain)
include hf

theorem regular_at {x : ℝ} (hx : x ∈ interval) : ContDiffAt ℝ 2 f x :=
  (hf x (subset hx)).contDiffAt (isOpen_Ioo.mem_nhds (subset hx))

theorem derivative_regular : ContDiffOn ℝ 1 (deriv f) domain :=
  hf.deriv_of_isOpen isOpen_Ioo (by norm_num)

theorem second_continuous : ContinuousOn (deriv (deriv f)) interval :=
  ((derivative_regular hf).deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn.mono subset

theorem has_deriv {x : ℝ} (hx : x ∈ interval) : HasDerivAt f (deriv f x) x :=
  ((regular_at hf hx).differentiableAt (by norm_num)).hasDerivAt

theorem has_second_deriv {x : ℝ} (hx : x ∈ interval) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  (((derivative_regular hf) x (subset hx)).contDiffAt
    (isOpen_Ioo.mem_nhds (subset hx))).differentiableAt (by norm_num) |>.hasDerivAt

theorem derivative_bounds : ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
    (∀ x ∈ interval, |deriv f x| ≤ L) ∧
    (∀ x ∈ interval, |deriv (deriv f) x| ≤ M) := by
  have hc1 := (derivative_regular hf).continuousOn.mono subset
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hc1.abs
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (second_continuous hf).abs
  have hbL : ∀ x ∈ interval, |deriv f x| ≤ L := fun x hx => hL ⟨x, hx, rfl⟩
  have hbM : ∀ x ∈ interval, |deriv (deriv f) x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  exact ⟨L, M, (abs_nonneg _).trans (hbL 0 (by norm_num [interval])),
    (abs_nonneg _).trans (hbM 0 (by norm_num [interval])), hbL, hbM⟩

theorem lipschitz {L : ℝ} (hL : ∀ x ∈ interval, |deriv f x| ≤ L)
    {x z : ℝ} (hx : x ∈ interval) (hz : z ∈ interval) : |f x - f z| ≤ L * |x - z| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (has_deriv hf hw).hasDerivWithinAt)
      (fun w hw => by simpa only [Real.norm_eq_abs] using hL w hw) hz hx

omit hf

def clamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem clamp_mem (x : ℝ) : clamp x ∈ interval :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_eq {x : ℝ} (hx : x ∈ interval) : clamp x = x := by
  rw [clamp, min_eq_right hx.2, max_eq_right hx.1]

def clipped (f : ℝ → ℝ) (x : ℝ) : ℝ := f (clamp x)

include hf in
theorem clipped_continuous : Continuous (clipped f) := by
  exact (hf.continuousOn.mono subset).comp_continuous
    (show Continuous clamp by unfold clamp; fun_prop) clamp_mem

theorem clipped_eq {x : ℝ} (hx : x ∈ interval) : clipped f x = f x := by
  rw [clipped, clamp_eq hx]

def sliceExtension (y : ℝ) : ℝ := SlicePrimitive.h y + SlicePrimitive.h (-y)

theorem sliceExtension_regular : ContDiffOn ℝ 2 sliceExtension domain := by
  intro y hy
  have hn : -y ∈ domain := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  exact ((SlicePrimitive.h_contDiffAt hy).add
    ((SlicePrimitive.h_contDiffAt hn).comp y contDiffAt_id.neg)).contDiffWithinAt

theorem sliceExtension_even : Function.Even sliceExtension := by
  intro y
  simp only [sliceExtension, neg_neg, add_comm]

theorem sliceExtension_eq {y : ℝ} (hy : y ∈ interval) : sliceExtension y = CountData.g y :=
  (SlicePrimitive.g_eq hy).symm

end Cubic.AllGaloisCounts.SmoothTraceData
