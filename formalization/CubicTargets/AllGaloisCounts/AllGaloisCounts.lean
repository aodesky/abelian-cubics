import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.AllGaloisCounts
open Cubic.AllGaloisCounts.CountData Filter Asymptotics

/-- `thm:allGaloisCounts`, with `H` tending to infinity through natural numbers. -/
def Claim : Prop :=
  (∀ G H, (galoisSet G H).Finite) ∧
  (fun H : ℕ => (N .trivial H : ℝ) - splitLeading * (H : ℝ) ^ 3) =O[atTop]
    (fun H : ℕ => (H : ℝ) ^ 2) ∧
  (fun H : ℕ => (N .quadratic H : ℝ) -
    (markedVolume * (H : ℝ) ^ 4 + (markedBoundary - 3 * splitLeading) * (H : ℝ) ^ 3))
      =O[atTop] (fun H : ℕ => (H : ℝ) ^ 2) ∧
  ∀ ε : ℝ, 0 < ε →
    (fun H : ℕ => (N .cyclic H : ℝ) - (H : ℝ) ^ 3 * P (Real.log H)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ (2 + ε)) ∧
    (fun H : ℕ => (N .symmetric H : ℝ) -
      (8 * (H : ℝ) ^ 6 + 4 * (H : ℝ) ^ 5 + (4 - markedVolume) * (H : ℝ) ^ 4 +
        (H : ℝ) ^ 3 * (6 - markedBoundary + 2 * splitLeading - P (Real.log H))))
      =O[atTop] (fun H : ℕ => (H : ℝ) ^ (2 + ε))
end CubicTargets.AllGaloisCounts.AllGaloisCounts
