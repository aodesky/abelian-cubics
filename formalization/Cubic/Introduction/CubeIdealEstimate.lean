import Cubic.Introduction.CubeIdealSummation
import Cubic.Introduction.CubeIdealMainTerm
import Cubic.Introduction.CubeIdealError

/-! Specializing the cited ideal estimate and removing the factor at three. -/

noncomputable section

namespace Cubic.Introduction.CubeIdealEstimate

open Filter Asymptotics CubeIdealSumData CubeIdealMainTerm
open Cubic.PoissonSummation Cubic.Counting.AsymptoticConstantScaling

theorem coefficient_estimate
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    (fun X : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (HeightCountingData.count n : ℂ)) -
        coefficientMainTerm c₂ c₁ X) =O[atTop] error := by
  have ht : Tendsto (fun X : ℝ => X / 3) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have h := CubeIdealEuler.estimate hKN
  have hd := (h.comp_tendsto ht).trans CubeIdealError.divide_three
  refine (h.sub hd).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hc : ∀ n : ℕ, (HeightCountingData.count n : ℂ) =
      (HeightCountingCoefficients.coefficient n : ℂ) := by
    intro n
    exact_mod_cast IdealHeightSeries.counts_eq_coefficient n
  simp only [hc]
  rw [CubeIdealSummation.summatory_difference,
    ← CubeIdealMainTerm.main_difference X hX.ne']
  dsimp [allMain]
  ring

end Cubic.Introduction.CubeIdealEstimate
