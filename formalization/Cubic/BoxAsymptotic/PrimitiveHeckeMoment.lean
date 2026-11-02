import Cubic.BoxAsymptotic.HeckeBlockLimits
import Cubic.BoxAsymptotic.MixedDyadicBound
import Cubic.BoxAsymptotic.AngularAFE

/-! The primitive second moment used in `lem:moment`. The actual forward and
dual AFE blocks have a summable majorant in the finite-dimensional Hilbert
space of frequencies. The common scale cancels in the dual prefactor, so
the argument introduces no `K^ε`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimitiveHeckeMoment

open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeCosineAFE
open Cubic.BoxAsymptotic.HeckeAFEScales Cubic.BoxAsymptotic.HeckeBlockMoments
open Cubic.BoxAsymptotic.HeckeAnalyticRealization Cubic.BoxAsymptotic.WeightedBlockBound
open Cubic.BoxAsymptotic.AngularMomentDyadic
open Cubic.Analysis.GammaAFEData (dualFactor)

theorem common_scale {K : ℝ} (hK : 2 ≤ K) (t : ℝ) :
    commonLength K t * Real.log (2 * commonLength K t) ^ 6 ≤ momentScale 6 K t := by
  obtain ⟨hY, _, hYK⟩ := common_bounds hK t
  have hl := Real.log_le_log (by linarith : 0 < 2 * commonLength K t)
    (by linarith : 2 * commonLength K t ≤ 2 * K + 2 * |t|)
  have hl0 : 0 ≤ Real.log (2 * commonLength K t) := Real.log_nonneg (by linarith)
  exact (mul_le_mul hYK (pow_le_pow_left₀ hl0 hl 6) (by positivity)
    (by linarith [abs_nonneg t])).trans (scale_six hK t)

/-- The literature assumptions supply analytic continuation, the generic AFE,
its weight estimates, Stirling, and the additive/binary sieve inequalities.
All their arithmetic specializations and the moment deduction are proved. -/
theorem bound
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    (hRM : CubicTargets.BoxAsymptotic.BinaryDecomposition.BlackBox)
    (hAFE : CubicTargets.BoxAsymptotic.GammaAFE.Identity)
    (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights)
    (hGamma : CubicTargets.BoxAsymptotic.GammaAFE.GammaRatio) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K t σ : ℝ), 2 ≤ K → 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      (∑ k ∈ evenModes K, ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2) ≤
        C * momentScale 6 K t := by
  classical
  obtain ⟨Cs, hCs, hS⟩ := PrimitiveAngularSieve.bound hLS hRM
  obtain ⟨L, V, ε, hL, _hRoots, ⟨Cw, hCw, hW⟩, hEq, ⟨Cp, hCp, hP⟩⟩ :=
    AngularAFE.«lem:angularAFE» hHecke hAFE hWeights hGamma
  let D := variationConstant Cw
  let M := 6 * D ^ 2 * Cs * (1 + Cp ^ 2)
  have hD : 0 < D := variationConstant_pos hCw.le
  have hM : 0 < M := by dsimp [M]; positivity
  let C := (Real.sqrt M * totalWeight) ^ 2
  have hC : 0 < C := by
    dsimp [C]
    exact sq_pos_of_pos (mul_pos (Real.sqrt_pos.mpr hM) totalWeight_pos)
  refine ⟨C, hC, fun K t σ hK hσ hσ' => ?_⟩
  let Y := commonLength K t
  let B := Y * Real.log (2 * Y) ^ 6
  have hY : 2 ≤ Y := (common_bounds hK t).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hl (k : ↥(evenModes K)) :=
    HeckeBlockLimits.limit hEq K t σ hK hσ hσ' k.property
  let p : ↥(evenModes K) → ℂ := fun k =>
    dualFactor (conductorScale k) (gammaShift k) (ε k) (σ + t * Complex.I)
  have hp (k : ↥(evenModes K)) : ‖p k‖ ≤ Cp * Y ^ (-2 * (σ - 1 / 2)) := by
    apply dual_common_bound hCp.le hK k.property σ t hσ (ε k)
    simpa using hP k (mem_evenModes.mp k.property).2 (frequency_ge_two hK k.property)
      (σ + t * Complex.I) (by simpa using hσ) (by simpa using hσ')
  let b : ℕ → ↥(evenModes K) → ℂ := fun j k =>
    forward V K t σ j k + p k * dual V K t σ j k
  have hb (j : ℕ) : (∑ k : ↥(evenModes K), ‖b j k‖ ^ 2) ≤ M * weight j ^ 2 * B := by
    have hf : (∑ k : ↥(evenModes K), ‖forward V K t σ j k‖ ^ 2) ≤
        (D * (1 / 8 : ℝ) ^ j) ^ 2 *
          (Cs * (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5) := by
      rw [Finset.sum_coe_sort (evenModes K) (fun k : ℤ => ‖forward V K t σ j k‖ ^ 2)]
      exact forward_bound hCw.le hW hS K t σ hK hσ hσ' j
    have hg : (∑ k : ↥(evenModes K), ‖dual V K t σ j k‖ ^ 2) ≤
        (D * (1 / 8 : ℝ) ^ j) ^ 2 * (((2 : ℝ) ^ j * Y) ^ (σ - 1 / 2)) ^ 2 *
          (Cs * (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5) := by
      rw [Finset.sum_coe_sort (evenModes K) (fun k : ℤ => ‖dual V K t σ j k‖ ^ 2)]
      exact dual_bound hCw.le hW hS K t σ hK hσ hσ' j
    have h := MixedDyadicBound.dyadic_bound Finset.univ
      (fun k : ↥(evenModes K) => forward V K t σ j k)
      (fun k : ↥(evenModes K) => dual V K t σ j k) p
      (by linarith : 0 ≤ K) (common_bounds hK t).2.1 hY hCs.le
      (sub_nonneg.mpr hσ) (by linarith : σ - 1 / 2 ≤ 1) j (fun k _ => hp k) hf hg
    exact h.trans_eq (by dsimp [M, B, Y]; ring)
  have h := square_limit_le (fun k : ↥(evenModes K) => L k (σ + t * Complex.I))
    b hM.le hB hl hb
  rw [Finset.sum_coe_sort (evenModes K)
    (fun k : ℤ => ‖L k (σ + t * Complex.I)‖ ^ 2)] at h
  have heq : (∑ k ∈ evenModes K, ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2) =
      ∑ k ∈ evenModes K, ‖L k (σ + t * Complex.I)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [AngularAFE.continuation_eq hHecke hL (mem_evenModes.mp hk).2
      (frequency_ge_two hK hk) (by simp; linarith : 0 < (σ + t * Complex.I).re)]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_left (common_scale hK t) hC.le)

end Cubic.BoxAsymptotic.PrimitiveHeckeMoment
