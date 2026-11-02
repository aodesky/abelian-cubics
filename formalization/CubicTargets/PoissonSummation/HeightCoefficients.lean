import Cubic.PoissonSummation.HeightCountingData
import Mathlib.Data.Nat.Factorization.Basic

/-! The two coefficient formulas in `rem:heightCoefficients`, for the actual
height-fiber cardinalities. The product formula is stated for positive indices. -/

namespace CubicTargets.PoissonSummation.HeightCoefficients
open Cubic.PoissonSummation.HeightCountingData

def Claim : Prop :=
  (∀ n : ℕ, 3 ∣ n → count n = 0) ∧
  (∀ n : ℕ, ¬ 3 ∣ n → (count n : ℤ) = divisorFormula n) ∧
  (∀ n : ℕ, 0 < n → ¬ 3 ∣ n →
    (count n : ℤ) = if ∀ p ∈ n.primeFactors, p % 3 = 2 → Even (n.factorization p)
      then ∏ p ∈ n.primeFactors.filter (fun p => p % 3 = 1),
        (3 * (n.factorization p : ℤ) + 1)
      else 0)

end CubicTargets.PoissonSummation.HeightCoefficients
