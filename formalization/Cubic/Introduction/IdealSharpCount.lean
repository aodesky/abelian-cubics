import Cubic.Introduction.CubeIdealEstimate
import Cubic.Counting.IntegralPointCount
import Cubic.Counting.AsymptoticPolynomialCount
import CubicTargets.Introduction.IdealRemark

/-! The sharper ideal estimate gives the paper's two counting results:
use `X=H²` for points, subtract split polynomials, and then use
`X=3H²+1` for the coefficient height. -/

noncomputable section

namespace Cubic.Introduction.IdealSharpCount

open Filter Asymptotics CubeIdealSumData CubeIdealMainTerm
open Cubic.Counting Cubic.PoissonSummation
open AsymptoticConstantScaling
open CubicTargets.Counting.WeightedPolynomialCount

private theorem real_of_complex {f g : ℝ → ℝ}
    (h : (fun X => (f X : ℂ)) =O[atTop] g) : f =O[atTop] g := by
  rw [← isBigO_norm_left] at h ⊢
  simpa only [Complex.norm_real] using h

theorem integral
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    (fun H : ℝ => (IntegralPointCountData.affineCount H : ℝ) -
      H ^ 2 * IntegralPointCountData.Q EulerKroneckerCalculation.value (Real.log H))
      =O[atTop] heightError := by
  have h := ((CubeIdealEstimate.coefficient_estimate hKN).comp_tendsto
    (tendsto_pow_atTop (by decide : 2 ≠ 0))).trans CubeIdealError.square
  apply real_of_complex
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  dsimp only [Function.comp_apply]
  rw [coefficient_main, Real.log_pow]
  have hc := IntegralPointCount.count_eq_sum H hH
  rw [← IntegralPointCount.affineCount_eq] at hc
  have hc' := congrArg (fun x : ℝ => (x : ℂ)) hc
  simp only [GeneralMonicData.d] at hc'
  push_cast at hc' ⊢
  rw [← hc']
  congr 2
  congr 1
  norm_num
  congr 1
  ring

theorem weighted_error :
    (fun X : ℝ => (Nat.card (countSet (Real.sqrt X)) : ℂ) -
      ((1 / 2 : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (HeightCountingData.count n : ℂ) -
        (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ)) * X))
      =O[atTop] (fun X : ℝ => Real.sqrt X) := by
  obtain ⟨K, hK⟩ := WeightedCount.«eqn:weightedPolynomialCount».2
  apply IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have h := hK X hX
  rw [← Real.norm_eq_abs, ← Complex.norm_real] at h
  push_cast at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg X)] using h

theorem toric
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    (fun X : ℝ => (Nat.card (countSet (Real.sqrt X)) : ℂ) -
      toricPolynomialMainTerm c₂ c₁ X) =O[atTop] error := by
  have hw := weighted_error.trans CubeIdealError.sqrt_error
  have hc := (CubeIdealEstimate.coefficient_estimate hKN).const_mul_left (1 / 2 : ℂ)
  exact (hw.add hc).congr_left (fun X => by
    dsimp [toricPolynomialMainTerm, coefficientMainTerm]
    ring)

theorem cyclic
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    (fun H : ℝ => (PolynomialCountData.polynomialCount H : ℝ) -
      (AsymptoticConstantsData.originalLeading * H ^ 2 * Real.log H +
        (AsymptoticConstantsData.originalLeading * Real.log (Real.sqrt 3) +
          AsymptoticConstantsData.originalLeading * AsymptoticConstantsData.originalSecondaryRatio -
          Real.pi / (3 * Real.sqrt 3)) * H ^ 2))
      =O[atTop] heightError := by
  have ht : Tendsto (fun H : ℝ => 3 * H ^ 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_const_mul_pow_atTop (by decide : 2 ≠ 0) (by norm_num : (0 : ℝ) < 3))
  have hc := ((toric hKN).comp_tendsto ht).trans CubeIdealError.shifted_square
  have hs := (AsymptoticHeightShift.main_term_height_shift c₂ c₁).trans
    (Real.isLittleO_log_id_atTop.isBigO.trans CubeIdealError.identity_height)
  apply real_of_complex
  refine (hc.add hs).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  dsimp only [Function.comp_apply]
  have he : PolynomialCountData.polynomialCount H =
      Nat.card (countSet (Real.sqrt (3 * H ^ 2 + 1))) := by
    rw [PolynomialCountData.polynomialCount, AsymptoticPolynomialCount.bounded_eq H hH,
      add_comm (1 : ℝ)]
  rw [AsymptoticConstantsAssembly.root_main_term expansion H]
  push_cast
  rw [he]
  ring

theorem claim
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    CubicTargets.Introduction.IdealRemark.SharpEstimate :=
  ⟨IntegralPointCount.affine_finite_counts,
    PolynomialCountFiniteness.boundedPolynomials_finite, integral hKN, cyclic hKN⟩

end Cubic.Introduction.IdealSharpCount
