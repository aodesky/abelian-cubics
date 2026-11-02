import CubicTargets.BoxAsymptotic.GammaAFE
import Cubic.BoxAsymptotic.HeckeAnalyticRealization

/-! Applying the textbook AFE to the constructed primitive Hecke functions.
These are the textbook cosine weights specified in the proof of
`lem:angularAFE`. The ideal coefficients and analytic continuation in the
application have already been independently constructed.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeCosineAFE

open Cubic.BoxAsymptotic.HeckePrimitiveCharacters
open Cubic.BoxAsymptotic.HeckeAnalyticRealization
open Cubic.BoxAsymptotic.HeckeSeriesConvergence
open Cubic.Analysis.GammaAFEData

def gammaShift (k : ℤ) : ℝ := (k.natAbs : ℝ) / 2

theorem gammaShift_ge_one {k : ℤ} (hk : 2 ≤ k) : 1 ≤ gammaShift k := by
  have habs : (2 : ℝ) ≤ k.natAbs := by
    exact_mod_cast (show (2 : ℤ) ≤ (k.natAbs : ℤ) by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]; exact hk)
  dsimp [gammaShift]
  linarith

theorem conductorScale_pos (k : ℤ) : 0 < conductorScale k := by
  unfold conductorScale
  split_ifs <;> positivity

theorem analytic_data
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    ∃ (Λ : ℂ → ℂ) (ε : ℂ),
      AnalyticData (coefficient (primitiveHom k)) (conductorScale k) (gammaShift k)
        (primitiveL hHecke k) Λ ε := by
  obtain ⟨Λ, ε, h⟩ := (exists_analytic hHecke hk hk0).choose_spec
  refine ⟨Λ, ε, ?_⟩
  have hp : primitiveL hHecke k = (exists_analytic hHecke hk hk0).choose := by
    rw [primitiveL, dif_pos ⟨hk, hk0⟩]
  rw [hp]
  refine ⟨h.entire, h.completed_entire, ?_, h.series_eq, ?_, h.root_number,
    h.functional_equation, h.growth⟩
  · exact coefficient_summable (primitiveHom k) (HeckeOmitThree.primitive_norm k)
  · intro s hs
    convert h.completion_eq s hs using 1
    simp only [completedFactor, PrimitiveHeckeData.completedFactor, gammaShift,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]

/-- Exact AFE and absolute convergence for the original norm-fiber
coefficients of the primitive ideal character. -/
theorem equation
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (hAFE : CubicTargets.BoxAsymptotic.GammaAFE.Identity)
    {k : ℤ} (hk : Even k) (hk2 : 2 ≤ k) (s : ℂ)
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 4) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      Summable (fun n => ‖weightedTerm (coefficient (primitiveHom k))
        (conductorScale k) (gammaShift k) s n‖) ∧
      Summable (fun n => ‖weightedTerm (fun n => star (coefficient (primitiveHom k) n))
        (conductorScale k) (gammaShift k) (1 - s) n‖) ∧
      primitiveL hHecke k s =
        (∑' n, weightedTerm (coefficient (primitiveHom k)) (conductorScale k) (gammaShift k) s n) +
        dualFactor (conductorScale k) (gammaShift k) ε s *
          ∑' n, weightedTerm (fun n => star (coefficient (primitiveHom k) n))
            (conductorScale k) (gammaShift k) (1 - s) n := by
  obtain ⟨Λ, ε, h⟩ := analytic_data hHecke hk (by omega : k ≠ 0)
  exact ⟨ε, h.root_number, hAFE _ _ _ _ _ _ (conductorScale_pos k) (gammaShift_ge_one hk2) h s hs hs'⟩

end Cubic.BoxAsymptotic.HeckeCosineAFE
