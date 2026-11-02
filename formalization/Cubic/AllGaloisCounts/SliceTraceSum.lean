import Cubic.AllGaloisCounts.SmoothTraceBoundary
import Cubic.AllGaloisCounts.LinearFactorSliceMoments
import Cubic.AllGaloisCounts.MarkedRootLatticeSum

/-! The second trapezoidal sum specialized to the actual marked-root slice. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceTraceSum
open CountData SmoothTraceData
open Cubic.Counting.GeneralMonicCount (T)

theorem estimate : ∃ K : ℝ, 0 ≤ K ∧ ∀ H : ℝ, 1 ≤ H →
    |(∑ a ∈ T H, g ((a : ℝ) / H)) -
      (H * markedVolume + (1 - 2 * Int.fract H) * markedBoundary)| ≤ K / H := by
  obtain ⟨K, hK, hb⟩ := SmoothTraceBoundary.estimate sliceExtension_regular sliceExtension_even
  refine ⟨K, hK, fun H hH => ?_⟩
  have hp : 0 < H := by linarith
  have hs : (∑ a ∈ T H, sliceExtension ((a : ℝ) / H)) = ∑ a ∈ T H, g ((a : ℝ) / H) :=
    Finset.sum_congr rfl (fun a ha => sliceExtension_eq (MarkedRootLatticeSum.scaled_parameter hp ha))
  have hi : (∫ y in (-1 : ℝ)..1, sliceExtension y) = markedVolume := by
    calc _ = ∫ y in (-1 : ℝ)..1, g y := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
          exact fun y hy => sliceExtension_eq hy
      _ = _ := SliceVolume.volume
  have he : sliceExtension 1 = markedBoundary :=
    (sliceExtension_eq (by norm_num [interval])).trans SlicePrimitive.boundary
  simpa only [hs, hi, he] using hb H hH

end Cubic.AllGaloisCounts.SliceTraceSum
