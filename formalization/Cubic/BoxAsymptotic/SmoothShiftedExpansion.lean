import Cubic.BoxAsymptotic.SmoothContourShift
import Cubic.BoxAsymptotic.SmoothMellinCount
import Cubic.BoxAsymptotic.ZeroMode

/-! The smoothed count minus its main term is the absolutely convergent sum
of the actual shifted mode integrals. This packages inversion and contour
shifting before the uniform moment estimate is applied. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothShiftedExpansion

open Complex MeasureTheory Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.Analysis.MellinDirichletPairing
open scoped ContDiff

/-- The analytic angular modes, with the separately constructed zero mode. -/
def mode (hHecke : PrimitiveHecke.BlackBox) (k : ℤ) : ℂ → ℂ :=
  if k = 0 then ZeroModeData.continuation else HeckeAnalyticRealization.angularF hHecke k

theorem mode_eq_series (hHecke : PrimitiveHecke.BlackBox)
    (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    mode hHecke k s = AngularSeriesData.series k s := by
  by_cases hk : k = 0
  · subst k
    rw [mode, if_pos rfl, AngularSeriesConvergence.series_zero]
    exact (ZeroModeSeries.series_hasSum s hs).tsum_eq.symm
  · rw [mode, if_neg hk]
    exact HeckeAnalyticRealization.angular_series hHecke hk s hs

theorem initial_pairing_eq (hHecke : PrimitiveHecke.BlackBox)
    (w : ℝ × ℝ → ℝ) (k : ℤ) :
    pairing 2 (mode hHecke k) (transform w k) =
      pairing 2 (AngularSeriesData.series k) (transform w k) := by
  unfold pairing
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mode_eq_series hHecke k _ (by simp)]

theorem shifted_expansion
    (hHecke : PrimitiveHecke.BlackBox)
    {w : ℝ × ℝ → ℝ} {X Θ θ₀ M η : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M 4) :
    HasSum (fun k : ℤ => pairing (1 / 2 + η) (mode hHecke k) (transform w k))
      (((∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (fun θ => w (n, θ)) : ℝ) : ℂ) -
        SmoothZeroResidue.residue w) := by
  have hinit := SmoothMellinCount.initial_expansion hw (by linarith) hΘ hM hp hs hb
  have hpole : HasSum (fun k : ℤ => if k = 0 then SmoothZeroResidue.residue w else 0)
      (SmoothZeroResidue.residue w) := hasSum_ite_eq 0 _
  apply (hinit.sub hpole).congr_fun
  intro k
  symm
  rw [← initial_pairing_eq hHecke]
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl, mode, if_pos rfl, SmoothContourShift.zero hw hX hΘ hη hη' hp hs]
    ring
  · rw [if_neg hk, sub_zero, mode, if_neg hk]
    exact SmoothContourShift.nonzero hHecke hw hX hΘ hη hη' hp hs k hk

end Cubic.BoxAsymptotic.SmoothShiftedExpansion
