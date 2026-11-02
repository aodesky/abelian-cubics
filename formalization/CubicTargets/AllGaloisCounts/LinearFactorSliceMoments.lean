import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.LinearFactorSliceMoments
open Cubic.AllGaloisCounts.CountData

/-- `lemma:linearFactorSliceMoments`, for the actual intersection-length integral. -/
def Claim : Prop :=
  Function.Even g ∧ ContDiffOn ℝ 2 g (Set.Icc (-1) 1) ∧
    (∫ y in (-1 : ℝ)..1, g y) = markedVolume ∧ g 1 = markedBoundary
end CubicTargets.AllGaloisCounts.LinearFactorSliceMoments
