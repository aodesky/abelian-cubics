import Cubic.BoxAsymptotic.HeckeDualFactor
import Cubic.BoxAsymptotic.WeightedBlockBound

/-! A single norm scale for every frequency in the dyadic interval. The
forward and dual weights share this scale, and the dual prefactor decreases
with it throughout the closed strip in the moment lemma. -/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeAFEScales

open Cubic.Analysis.GammaAFEData
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeCosineAFE
open Cubic.BoxAsymptotic.HeckeCosineWeights Cubic.BoxAsymptotic.WeightedBlockBound
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums

def commonLength (K t : ℝ) : ℝ := 1 + K / 2 + |t|

theorem common_bounds {K : ℝ} (hK : 2 ≤ K) (t : ℝ) :
    2 ≤ commonLength K t ∧ K ≤ 2 * commonLength K t ∧ commonLength K t ≤ K + |t| := by
  unfold commonLength
  constructor
  · linarith [abs_nonneg t]
  constructor <;> linarith [abs_nonneg t]

theorem frequency_ge_two {K : ℝ} (hK : 2 ≤ K) {k : ℤ} (hk : k ∈ evenModes K) : 2 ≤ k := by
  have h := (mem_evenModes.mp hk).1.1
  have : (2 : ℝ) < k := lt_of_le_of_lt hK h
  exact_mod_cast this.le

theorem mode_band {K : ℝ} (hK : 2 ≤ K) {k : ℤ} (hk : k ∈ evenModes K) (σ t : ℝ) :
    commonLength K t ≤ modeLength k (σ + t * Complex.I) ∧
      modeLength k (σ + t * Complex.I) ≤ 3 * commonLength K t := by
  have hp : 0 ≤ k := le_trans (by norm_num) (frequency_ge_two hK hk)
  have hkR : (k.natAbs : ℝ) = (k : ℝ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hp]
  obtain ⟨hlo, hhi⟩ := (mem_evenModes.mp hk).1
  simp only [commonLength, modeLength, gammaShift, hkR, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  constructor <;> linarith [abs_nonneg t]

@[simp] theorem modeLength_one_sub (k : ℤ) (s : ℂ) : modeLength k (1 - s) = modeLength k s := by
  simp [modeLength]

theorem uniform_control (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (u : ℂ),
      2 ≤ k → 1 / 4 ≤ u.re → u.re ≤ 3 / 4 →
      Control (weight (conductorScale k) (gammaShift k) u) (modeLength k u) C := by
  obtain ⟨C, hC, hb⟩ := HeckeCosineWeights.bounds hWeights
  refine ⟨C, hC, fun k u hk hu hu' => ?_⟩
  obtain ⟨hd, hc, hs, hs', hl, hl'⟩ := hb k u hk hu hu'
  exact ⟨hd, hc, hs, hs', hl, hl'⟩

theorem dual_common_bound {C : ℝ} (hC : 0 ≤ C) {K : ℝ} (hK : 2 ≤ K)
    {k : ℤ} (hk : k ∈ evenModes K) (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (ε : ℂ)
    (hp : ‖dualFactor (conductorScale k) (gammaShift k) ε (σ + t * Complex.I)‖ ≤
      C * modeLength k (σ + t * Complex.I) ^ (1 - 2 * σ)) :
    ‖dualFactor (conductorScale k) (gammaShift k) ε (σ + t * Complex.I)‖ ≤
      C * commonLength K t ^ (-2 * (σ - 1 / 2)) := by
  have hY : 0 < commonLength K t := lt_of_lt_of_le (by norm_num) (common_bounds hK t).1
  have hr := Real.rpow_le_rpow_of_nonpos hY (mode_band hK hk σ t).1
    (by linarith : 1 - 2 * σ ≤ 0)
  have he : 1 - 2 * σ = -2 * (σ - 1 / 2) := by ring
  exact hp.trans (by simpa only [he] using mul_le_mul_of_nonneg_left hr hC)

end Cubic.BoxAsymptotic.HeckeAFEScales
