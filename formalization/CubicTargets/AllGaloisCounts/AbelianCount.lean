import Cubic.AllGaloisCounts.AbelianCountData

namespace CubicTargets.AllGaloisCounts.AbelianCount
open Cubic.AllGaloisCounts.AbelianCountData Cubic.AllGaloisCounts.CountData
open Filter Asymptotics

def Claim : Prop :=
  (∀ H, (abelianSet H).Finite) ∧
  ∀ ε : ℝ, 0 < ε →
    (fun H : ℝ => (abelianCount H : ℝ) -
      (R H + H ^ 3 * (P (Real.log H) - 40 * Real.pi * Real.sqrt 3 / 81)))
      =O[atTop] (fun H : ℝ => H ^ (2 + ε))

end CubicTargets.AllGaloisCounts.AbelianCount
