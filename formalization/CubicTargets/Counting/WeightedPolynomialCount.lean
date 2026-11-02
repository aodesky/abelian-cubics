import Cubic.Counting.PolynomialCountData
import Cubic.PoissonSummation.HeightCountingData
import CubicTargets.Counting.EllipseLatticeCount

/-!
# `eqn:weightedPolynomialCount`

`Σ_{f ∈ F, H(f) ≤ √X} 1 = ½ Σ_{n ≤ X} d_n − πX/(9√3) + O(√X)` for `X ≥ 1`.

`F` is the set of integer cubics `t³-t²+at+b` with Galois group `C₃`
(`PolynomialCountData.cyclicPolynomials`). `d_n` is the number of `D₀`-integral
rational points of toric height `√n` (`HeightCountingData.count`), which are the
Dirichlet coefficients of `Z₀(s)`. `H(f) = √(1-3a)`, which by `prop:canonicalHeight`
is the toric height of every integral point with characteristic polynomial `f`.
-/

noncomputable section

namespace CubicTargets.Counting.WeightedPolynomialCount

open Cubic.Counting.PolynomialCountData

/-- The toric height `H(f) = √(1-3a)` of `f = t³-t²+at+b`. -/
def toricHeight (f : Polynomial ℤ) : ℝ := Real.sqrt (1 - 3 * (f.coeff 1 : ℝ))

/-- Polynomials in `F` of toric height at most `H`. -/
def countSet (H : ℝ) : Set (Polynomial ℤ) := {f | f ∈ cyclicPolynomials ∧ toricHeight f ≤ H}

def ExactClaim : Prop := ∀ H : ℝ, 1 ≤ H → (countSet H).Finite ∧
  (Nat.card (countSet H) : ℝ) =
    (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊H ^ 2⌋₊,
        (Cubic.PoissonSummation.HeightCountingData.count n : ℝ) -
      (1 / 6) * Nat.card (EllipseLatticeCount.latticePoints H)

/-- The current displayed equation, after inserting the ellipse estimate. -/
def Claim : Prop :=
  (∀ X : ℝ, 1 ≤ X → (countSet (Real.sqrt X)).Finite) ∧
    ∃ K : ℝ, ∀ X : ℝ, 1 ≤ X →
      |(Nat.card (countSet (Real.sqrt X)) : ℝ) -
        ((1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (Cubic.PoissonSummation.HeightCountingData.count n : ℝ) -
            Real.pi / (9 * Real.sqrt 3) * X)| ≤ K * Real.sqrt X

end CubicTargets.Counting.WeightedPolynomialCount
