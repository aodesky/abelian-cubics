import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.MarkedLinearFactorCount
open Cubic.AllGaloisCounts.CountData Filter Asymptotics

/-- `prop:markedLinearFactorCount`, counting distinct marked roots of each polynomial. -/
def Claim : Prop :=
  (∀ H : ℝ, (markedSet H).Finite) ∧
  (fun H : ℝ => (markedCount H : ℝ) - R H) =O[atTop] (fun H : ℝ => H ^ 2)
end CubicTargets.AllGaloisCounts.MarkedLinearFactorCount
