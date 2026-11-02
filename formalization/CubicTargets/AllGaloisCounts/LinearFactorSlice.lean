import Cubic.AllGaloisCounts.CountData

namespace CubicTargets.AllGaloisCounts.LinearFactorSlice
open Cubic.AllGaloisCounts.CountData MeasureTheory

/-- `eqn:linearFactorSlice`: genuine interval lengths and the value at zero. -/
def Claim : Prop :=
  (∀ y : ℝ, F 0 y = 2) ∧ ∀ x : ℝ, x ≠ 0 → ∀ y : ℝ,
    F x y = volume.real (Set.Icc (x ^ 2 + x * y - 1) (x ^ 2 + x * y + 1) ∩
      Set.Icc (-|x|⁻¹) |x|⁻¹)
end CubicTargets.AllGaloisCounts.LinearFactorSlice
