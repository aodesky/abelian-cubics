import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.RealHeightBounds
open Cubic.AllGaloisCounts.CountData Filter Asymptotics

/-- `rem:realHeightBounds`, retaining the floor terms for arbitrary real heights. -/
def Claim : Prop :=
  (∀ H : ℝ, 0 ≤ H → (Nat.card (cubicBox H) : ℝ) = boxFormula H) ∧
  (fun H : ℝ => (N .trivial H : ℝ) - splitLeading * H ^ 3) =O[atTop]
    (fun H : ℝ => H ^ 2) ∧
  (fun H : ℝ => (markedCount H : ℝ) - R H) =O[atTop] (fun H : ℝ => H ^ 2) ∧
  (fun H : ℝ => (N .quadratic H : ℝ) - (R H - 3 * splitLeading * H ^ 3))
    =O[atTop] (fun H : ℝ => H ^ 2) ∧
  ∀ ε : ℝ, 0 < ε →
    (fun H : ℝ => (N .cyclic H : ℝ) - H ^ 3 * P (Real.log H)) =O[atTop]
      (fun H : ℝ => H ^ (2 + ε)) ∧
    (fun H : ℝ => (N .symmetric H : ℝ) -
      (boxFormula H - R H - H ^ 3 * (P (Real.log H) - 2 * splitLeading)))
      =O[atTop] (fun H : ℝ => H ^ (2 + ε))
end CubicTargets.AllGaloisCounts.RealHeightBounds
