import Cubic.BoxAsymptotic.SmoothProductWeight
import CubicTargets.BoxAsymptotic.SmoothSector

/-! Specialization of the full smoothing statement to the product profiles
used by the geometric box-counting argument. Smoothness and the uniform
derivative bound are proved for those actual wrapped weights. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothProductCounting

open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothProductWeight

theorem of_full (h : SmoothSectorClaim) : SmoothSectorCounting := by
  obtain ⟨A, J, C, hC, hsmooth⟩ := h
  refine ⟨ZeroModeData.b₀, fun Φ Ψ hΦ hΨ hsΦ hsΨ => ?_⟩
  obtain ⟨M, hM, hb⟩ := derivative_bound hΦ hΨ hsΦ hsΨ J
  refine ⟨(A : ℝ), C * M, fun X Θ θ₀ hX hΘ hΘ' => ?_⟩
  have hh := hsmooth X Θ θ₀ M (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2)
    hX hΘ (by linarith) hM (smooth hΦ hΨ hsΨ hΘ hΘ')
    (periodic Φ Ψ X Θ θ₀) (support hsΦ hsΨ (by linarith) hΘ) (hb X Θ θ₀ hΘ hΘ')
  simpa only [one_div, Real.rpow_natCast] using hh

end Cubic.BoxAsymptotic.SmoothProductCounting
