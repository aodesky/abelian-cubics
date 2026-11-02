import Cubic.BoxAsymptotic.HeckeAFEScales
import Cubic.BoxAsymptotic.PrimitiveAngularSieve
import Cubic.BoxAsymptotic.AngularSieveScaling

/-! Applying the maximal sieve to the actual forward and dual AFE blocks.
The dual coefficients are rescaled through the current norm cutoff; the
frequency-dependent weights are handled by their proved variation bound.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeBlockMoments

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.HeckeCosineAFE Cubic.BoxAsymptotic.HeckeCosineWeights
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeAFEScales
open Cubic.BoxAsymptotic.WeightedBlockBound Cubic.BoxAsymptotic.WeightedIdealBlocks

def SieveEstimate (C : ℝ) : Prop :=
  ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y → ∀ (a : Ideal Integers → ℂ),
    (∀ I ∈ idealBall Y, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
    ((∑ k ∈ evenModes K, maximal (primitivePsi k) a Y ^ 2) ≤
      C * (K + Y) * Real.log (2 * Y) ^ 5) ∧
    ((∑ k ∈ evenModes K, maximal (conjugate (primitivePsi k)) a Y ^ 2) ≤
      C * (K + Y) * Real.log (2 * Y) ^ 5)

def WeightEstimate (V : ℤ → ℂ → ℝ → ℂ) (C : ℝ) : Prop :=
  ∀ (k : ℤ), Even k → 2 ≤ k → ∀ u : ℂ, 1 / 4 ≤ u.re → u.re ≤ 3 / 4 →
    Control (V k u) (modeLength k u) C

def forward (V : ℤ → ℂ → ℝ → ℂ) (K t σ : ℝ) (j : ℕ) (k : ℤ) : ℂ :=
  block (primitivePsi k) (HeckeNormWeights.coefficient (σ + t * Complex.I))
    (commonLength K t) (V k (σ + t * Complex.I)) j

def dual (V : ℤ → ℂ → ℝ → ℂ) (K t σ : ℝ) (j : ℕ) (k : ℤ) : ℂ :=
  block (conjugate (primitivePsi k)) (HeckeNormWeights.coefficient (1 - (σ + t * Complex.I)))
    (commonLength K t) (V k (1 - (σ + t * Complex.I))) j

theorem cutoff_ge_two {K : ℝ} (hK : 2 ≤ K) (t : ℝ) (j : ℕ) :
    2 ≤ (2 : ℝ) ^ j * commonLength K t := by
  have hY := (common_bounds hK t).1
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

theorem forward_bound {V : ℤ → ℂ → ℝ → ℂ} {Cw Cs : ℝ} (hCw : 0 ≤ Cw) (hW : WeightEstimate V Cw) (hS : SieveEstimate Cs)
    (K t σ : ℝ) (hK : 2 ≤ K) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 4) (j : ℕ) :
    (∑ k ∈ evenModes K, ‖forward V K t σ j k‖ ^ 2) ≤
      (variationConstant Cw * (1 / 8 : ℝ) ^ j) ^ 2 *
        (Cs * (K + (2 : ℝ) ^ j * commonLength K t) *
          Real.log (2 * ((2 : ℝ) ^ j * commonLength K t)) ^ 5) := by
  apply mean_bound (evenModes K) primitivePsi (HeckeNormWeights.coefficient (σ + t * Complex.I))
    (fun k => V k (σ + t * Complex.I)) (fun k => modeLength k (σ + t * Complex.I))
    (common_bounds hK t).1 hCw (fun k hk => mode_band hK hk σ t)
    (fun k hk => hW k (mem_evenModes.mp hk).2 (frequency_ge_two hK hk) _ (by simp; linarith) (by simpa)) j
  exact (hS K _ hK (cutoff_ge_two hK t j) _
    (fun I hI => HeckeNormWeights.forward_bound hI (by simpa using hσ))).1

set_option maxHeartbeats 800000 in
theorem dual_bound {V : ℤ → ℂ → ℝ → ℂ} {Cw Cs : ℝ} (hCw : 0 ≤ Cw) (hW : WeightEstimate V Cw) (hS : SieveEstimate Cs)
    (K t σ : ℝ) (hK : 2 ≤ K) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 4) (j : ℕ) :
    (∑ k ∈ evenModes K, ‖dual V K t σ j k‖ ^ 2) ≤
      (variationConstant Cw * (1 / 8 : ℝ) ^ j) ^ 2 *
        (((2 : ℝ) ^ j * commonLength K t) ^ (σ - 1 / 2)) ^ 2 *
        (Cs * (K + (2 : ℝ) ^ j * commonLength K t) *
          Real.log (2 * ((2 : ℝ) ^ j * commonLength K t)) ^ 5) := by
  have he : (1 : ℂ) - (σ + t * Complex.I) = ((1 / 2 - (σ - 1 / 2) : ℝ) : ℂ) + (-t) * Complex.I := by
    push_cast
    ring
  have hcoef (I : Ideal Integers) (hI : I ∈ idealBall ((2 : ℝ) ^ j * commonLength K t)) :
      ‖HeckeNormWeights.coefficient (1 - (σ + t * Complex.I)) I‖ ≤
        ((2 : ℝ) ^ j * commonLength K t) ^ (σ - 1 / 2) / Real.sqrt (Ideal.absNorm I) := by
    rw [he]
    simpa only [Complex.ofReal_neg] using
      HeckeNormWeights.dual_bound (η := σ - 1 / 2) hI (sub_nonneg.mpr hσ) (-t)
  have hb := AngularSieveScaling.scaled_bound (evenModes K) (fun k => conjugate (primitivePsi k))
    (Y := (2 : ℝ) ^ j * commonLength K t)
    (R := Cs * (K + (2 : ℝ) ^ j * commonLength K t) *
      Real.log (2 * ((2 : ℝ) ^ j * commonLength K t)) ^ 5)
    (B := ((2 : ℝ) ^ j * commonLength K t) ^ (σ - 1 / 2))
    (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (cutoff_ge_two hK t j)) _)
    (fun a ha => (hS K _ hK (cutoff_ge_two hK t j) a ha).2)
    (HeckeNormWeights.coefficient (1 - (σ + t * Complex.I)))
    hcoef
  have hw (k : ℤ) (hk : k ∈ evenModes K) :
      Control (V k (1 - (σ + t * Complex.I))) (modeLength k (σ + t * Complex.I)) Cw := by
    simpa only [modeLength_one_sub] using
      hW k (mem_evenModes.mp hk).2 (frequency_ge_two hK hk) (1 - (σ + t * Complex.I)) (by simp; linarith) (by simp; linarith)
  have h := mean_bound (evenModes K) (fun k => conjugate (primitivePsi k))
    (HeckeNormWeights.coefficient (1 - (σ + t * Complex.I)))
    (fun k => V k (1 - (σ + t * Complex.I))) (fun k => modeLength k (σ + t * Complex.I))
    (common_bounds hK t).1 hCw (fun k hk => mode_band hK hk σ t) hw j hb
  exact h.trans_eq (by ring)

end Cubic.BoxAsymptotic.HeckeBlockMoments
