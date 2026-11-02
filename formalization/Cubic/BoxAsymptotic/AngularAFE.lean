import CubicTargets.BoxAsymptotic.AngularAFE
import Cubic.BoxAsymptotic.HeckeDualFactor
import Cubic.BoxAsymptotic.AngularContinuation

/-! `lem:angularAFE`: the textbook cosine construction supplies the weights.
The same construction, Gamma normalization, conductor comparison, and uniform
estimates are specified in the manuscript. The conclusion exposes only the
properties used by the subsequent moment proof. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularAFE

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularAFEData Cubic.BoxAsymptotic.HeckeWeightedSeries
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeAnalyticRealization
open Cubic.BoxAsymptotic.HeckeCosineAFE Cubic.BoxAsymptotic.HeckeCosineWeights
open Cubic.BoxAsymptotic.HeckeSeriesConvergence Cubic.BoxAsymptotic.IdealAngularData
open Cubic.Analysis.GammaAFEData

/-- Uniqueness ties the existential primitive continuation in the lemma to the
one already used in the angular Euler products. -/
theorem continuation_eq
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {L : ℤ → ℂ → ℂ} (hL : Continuation L) {k : ℤ} (hk : Even k) (hk2 : 2 ≤ k)
    {s : ℂ} (hs : 0 < s.re) : L k s = primitiveL hHecke k s := by
  apply AngularContinuation.halfPlane_eq (by norm_num : (0 : ℝ) < 1)
    (hL k hk hk2).1.differentiableOn (primitive_entire hHecke hk (by omega)).differentiableOn ?_ hs
  intro z hz
  rw [(hL k hk hk2).2 z hz, primitive_series hHecke hk (by omega) z hz]

theorem «lem:angularAFE»
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (hAFE : CubicTargets.BoxAsymptotic.GammaAFE.Identity)
    (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights)
    (hGamma : CubicTargets.BoxAsymptotic.GammaAFE.GammaRatio) :
    CubicTargets.BoxAsymptotic.AngularAFEClaim := by
  classical
  let V (k : ℤ) (u : ℂ) := weight (conductorScale k) (gammaShift k) u
  let ε (k : ℤ) : ℂ := if h : Even k ∧ 2 ≤ k then
    (analytic_data hHecke h.1 (by omega : k ≠ 0)).choose_spec.choose else 1
  have hdata (k : ℤ) (hk : Even k) (hk2 : 2 ≤ k) :
      ∃ Λ : ℂ → ℂ, AnalyticData (coefficient (primitiveHom k))
        (conductorScale k) (gammaShift k) (primitiveL hHecke k) Λ (ε k) := by
    refine ⟨(analytic_data hHecke hk (by omega : k ≠ 0)).choose, ?_⟩
    dsimp only [ε]
    rw [dif_pos (show Even k ∧ 2 ≤ k from ⟨hk, hk2⟩)]
    exact (analytic_data hHecke hk (by omega : k ≠ 0)).choose_spec.choose_spec
  obtain ⟨Cw, hCw, hw⟩ := HeckeCosineWeights.bounds hWeights
  have hcontrol : WeightBounds V := by
    refine ⟨Cw, hCw, fun k _ hk u hu hu' => ?_⟩
    obtain ⟨hd, hc, h1, h2, h3, h4⟩ := hw k u hk hu hu'
    exact ⟨hd, hc, h1, h2, h3, h4⟩
  refine ⟨primitiveL hHecke, V, ε, ?_, ?_, hcontrol, ?_, ?_⟩
  · intro k hk hk2
    exact ⟨primitive_entire hHecke hk (by omega), primitive_series hHecke hk (by omega)⟩
  · intro k hk hk2
    obtain ⟨Λ, hd⟩ := hdata k hk hk2
    exact ⟨Λ, hd.completed_entire, hd.completion_eq, hd.functional_equation⟩
  · intro k hk hk2
    obtain ⟨Λ, hd⟩ := hdata k hk hk2
    refine ⟨hd.root_number, fun s hs hs' => ?_⟩
    have hs0 : 1 / 4 ≤ s.re := by linarith
    have hd0 : 1 / 4 ≤ (1 - s).re := by simp; linarith
    have hd1 : (1 - s).re ≤ 3 / 4 := by simp; linarith
    have ha := absolute (primitivePsi k) (norm_primitivePsi_le k) s (by linarith)
      (V k s) (hw k s hk2 hs0 hs').2.2.2.2.1
    have hb := absolute (fun I => star (primitivePsi k I))
      (fun I => by simpa using norm_primitivePsi_le k I) (1 - s) (by simp; linarith)
      (V k (1 - s)) (hw k (1 - s) hk2 hd0 hd1).2.2.2.2.1
    refine ⟨ha, hb, ?_⟩
    have he := (hAFE _ _ _ _ _ _ (conductorScale_pos k) (gammaShift_ge_one hk2) hd s hs hs').2.2
    have hc : (primitiveHom k : Ideal Integers → ℂ) = primitivePsi k := funext (primitiveHom_eq k)
    have hdc : coefficient (fun I => star (primitivePsi k I)) =
        fun n => star (coefficient (primitivePsi k) n) := funext (coefficient_conjugate (primitivePsi k))
    rw [sum_eq _ _ _ ha, sum_eq _ _ _ hb]
    simpa only [V, weightedTerm, hc, hdc] using he
  · obtain ⟨Cp, hCp, hp⟩ := HeckeDualFactor.bound hGamma
    refine ⟨Cp, hCp, fun k hk hk2 s hs hs' => ?_⟩
    obtain ⟨Λ, hd⟩ := hdata k hk hk2
    exact hp k (ε k) s hk2 hd.root_number hs hs'

end Cubic.BoxAsymptotic.AngularAFE
