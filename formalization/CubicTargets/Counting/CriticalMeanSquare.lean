import Cubic.Counting.HeightCoefficientData
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CubicTargets.Counting.CriticalMeanSquare
open Cubic.Counting.HeightCoefficientData

def Claim : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
  (∫ t in (1 : ℝ)..T, ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
    C * T * (Real.log T) ^ 2

end CubicTargets.Counting.CriticalMeanSquare
