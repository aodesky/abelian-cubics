import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.SplitCubicCount
open Cubic.AllGaloisCounts.CountData Filter Asymptotics

/-- `lemma:splitCubicCount`, at arbitrary real heights, including repeated roots. -/
def Claim : Prop :=
  (∀ H : ℝ, (galoisSet .trivial H).Finite) ∧
  (fun H : ℝ => (N .trivial H : ℝ) - splitLeading * H ^ 3) =O[atTop]
    (fun H : ℝ => H ^ 2)
end CubicTargets.AllGaloisCounts.SplitCubicCount
