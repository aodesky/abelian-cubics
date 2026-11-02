import Cubic.BoxAsymptotic.SmoothUniformEstimate
import Cubic.BoxAsymptotic.SmoothContourScale
import Cubic.BoxAsymptotic.AngularMoment
import CubicTargets.BoxAsymptotic.SmoothSector

/-! `lem:smooth`: the full uniform smoothed-sector estimate, for the actual
angular counting measures and the actual Laurent coefficients of `F₀`.
The only external inputs are those already used for `lem:moment`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothSector

open CubicTargets.BoxAsymptotic

/-- Fourier--Mellin inversion, the zero-mode residue, and the first angular
moment imply the full estimate with constants uniform in the test weight. -/
theorem of_moment
    (hHecke : PrimitiveHecke.BlackBox)
    (hmoment : AngularMomentClaim) : SmoothSectorClaim := by
  obtain ⟨A, J, C, hC, h⟩ := SmoothUniformEstimate.estimate hHecke hmoment
  refine ⟨A + 4, J, C * Real.exp 1 * 4 ^ 4 * 2 ^ A, by positivity, ?_⟩
  intro X Θ θ₀ M w hX hΘ hΘ' hM hw hp hs hb
  let D := 2 * X + Θ⁻¹
  let η := (4 * Real.log D)⁻¹
  obtain ⟨hD, hDΘ, hL, hL', hXD⟩ := SmoothContourScale.scale_conditions hX hΘ hΘ'
  obtain ⟨hη, hη'⟩ := SmoothContourScale.eta_conditions hL
  have hrad := SmoothContourScale.radial_bound (by linarith : 0 < X) hXD hL
  have hlog := SmoothContourScale.logarithmic_bound
    (show 2 ≤ D by dsimp [D]; have := inv_pos.mpr hΘ; linarith) hL A
  calc
    _ ≤ C * M * X ^ (1 / 2 + η) * η⁻¹ ^ 4 * Real.log (2 * D) ^ A :=
      h X Θ θ₀ M η D w (by linarith) hΘ hΘ' hM hη hη' hD hDΘ hL' hw hp hs hb
    _ = (C * M * X ^ (1 / 2 + η)) * (η⁻¹ ^ 4 * Real.log (2 * D) ^ A) := by ring
    _ ≤ (C * M * (Real.exp 1 * Real.sqrt X)) *
        ((4 : ℝ) ^ 4 * 2 ^ A * Real.log D ^ (A + 4)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrad (by positivity)) hlog
        (by positivity) (by positivity)
    _ = _ := by dsimp [D]; ring

/-- The full `lem:smooth`, conditional only on the precisely stated literature
inputs used to establish the angular moment. No smoothing estimate is assumed. -/
theorem «lem:smooth»
    (hLS : AdditiveLargeSieve.BlackBox)
    (hRM : BinaryDecomposition.BlackBox)
    (hHecke : PrimitiveHecke.BlackBox)
    (hAFE : GammaAFE.Identity)
    (hWeights : GammaAFE.Weights)
    (hGamma : GammaAFE.GammaRatio) : SmoothSectorClaim := by
  exact of_moment hHecke
    (AngularMoment.«lem:moment» hLS hRM hHecke hAFE hWeights hGamma)

end Cubic.BoxAsymptotic.SmoothSector
