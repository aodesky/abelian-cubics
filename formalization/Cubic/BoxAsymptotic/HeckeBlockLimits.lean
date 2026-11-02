import Cubic.BoxAsymptotic.HeckeBlockMoments
import Cubic.BoxAsymptotic.AngularAFEData

/-! Identification of the limit of the actual AFE blocks. Both ideal series
are absolutely convergent by a direct Dedekind-zeta majorant; the norm-fiber
AFE and its complex-conjugate dual coefficients then identify their sum.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeBlockLimits

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.HeckeCosineAFE Cubic.BoxAsymptotic.HeckeCosineWeights
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeAFEScales
open Cubic.BoxAsymptotic.HeckeAnalyticRealization Cubic.BoxAsymptotic.HeckeBlockMoments
open Cubic.BoxAsymptotic.WeightedIdealBlocks Cubic.BoxAsymptotic.HeckeWeightedSeries
open Cubic.Analysis.GammaAFEData
open Filter
open scoped Topology

theorem limit {L : ℤ → ℂ → ℂ} {V : ℤ → ℂ → ℝ → ℂ} {ε : ℤ → ℂ}
    (hAFE : AngularAFEData.Equations L V ε)
    (K t σ : ℝ) (hK : 2 ≤ K) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 4)
    {k : ℤ} (hk : k ∈ evenModes K) :
      Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        (forward V K t σ j k + dualFactor (conductorScale k) (gammaShift k) (ε k) (σ + t * Complex.I) *
          dual V K t σ j k)) atTop (𝓝 (L k (σ + t * Complex.I))) := by
  let s : ℂ := σ + t * Complex.I
  let Y := commonLength K t
  have hY : 0 < Y := lt_of_lt_of_le (by norm_num) (common_bounds hK t).1
  obtain ⟨ha, had, he⟩ := (hAFE k (mem_evenModes.mp hk).2 (frequency_ge_two hK hk)).2
    s (by simpa [s] using hσ) (by simpa [s] using hσ')
  have hscale : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * Y) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hY
  have hf := (initial_limit (primitivePsi k) s (V k s) ha).comp hscale
  have hd := (initial_limit (conjugate (primitivePsi k)) (1 - s) (V k (1 - s)) had).comp hscale
  have hh := hf.add (hd.const_mul (dualFactor (conductorScale k) (gammaShift k) (ε k) s))
  change Tendsto _ _ (𝓝 (L k s))
  rw [he]
  apply hh.congr
  intro n
  dsimp only [Function.comp_apply]
  simp only [forward, dual, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [partial_blocks (primitivePsi k) _ (commonLength K t) hY.le,
    partial_blocks (conjugate (primitivePsi k)) _ (commonLength K t) hY.le]

end Cubic.BoxAsymptotic.HeckeBlockLimits
