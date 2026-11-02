import Cubic.Counting.PolynomialCountData
import Cubic.PoissonSummation.ResidueParts
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `thm:exactFormula`

"For any `H ≥ 1` let `E_H ⊂ ℝ²` be the ellipse `x²+y²+xy−x−y = (H²−1)/3`. If
`t³−t²+at+b ∈ F` then `a ≤ 0`. Fix `a ∈ ℤ_{≤0}`. The number of polynomials of the form
`t³−t²+at+b ∈ F` for any `b ∈ ℤ` is equal to
`½ Σ_{d | 1−3a} 3^{ω(P₁(d))} (−1)^{Ω(P₂(d))} − ⅙ #E_{√(1−3a)}(ℤ)`."

* `F` is `PolynomialCountData.cyclicPolynomials`. The polynomials with linear
  coefficient `a` are counted through `b ↦ t³−t²+at+b`, which is injective.
* `E_H(ℤ)` is the set of integer points on the curve (an equation, not the region).
* `P_j(d) = primeResiduePart j d`, the largest divisor of `d` divisible only by primes
  `≡ j (mod 3)`. `ω` and `Ω` are mathlib's `cardDistinctFactors` and `cardFactors`.
* Finiteness of both counted sets is part of the conclusion, so `Nat.card` cannot hide
  an infinite set.
-/

noncomputable section

namespace CubicTargets.Counting.ExactFormula

open Cubic.Counting.PolynomialCountData

/-- The integer points `E_H(ℤ)` of the ellipse `x²+y²+xy−x−y = (H²−1)/3`. -/
def ellipsePoints (H : ℝ) : Set (ℤ × ℤ) :=
  {p | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) - p.1 - p.2 = (H ^ 2 - 1) / 3}

/-- The `b` with `t³−t²+at+b ∈ F`. -/
def fibre (a : ℤ) : Set ℤ := {b | traceOneCubic a b ∈ cyclicPolynomials}

/-- `Σ_{d | n} 3^{ω(P₁(d))} (−1)^{Ω(P₂(d))}`. -/
def divisorSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors,
    (3 : ℤ) ^ ArithmeticFunction.cardDistinctFactors
        (Cubic.PoissonSummation.primeResiduePart 1 d) *
      (-1 : ℤ) ^ ArithmeticFunction.cardFactors (Cubic.PoissonSummation.primeResiduePart 2 d)

def Claim : Prop :=
  (∀ a b : ℤ, traceOneCubic a b ∈ cyclicPolynomials → a ≤ 0) ∧
    ∀ a : ℤ, a ≤ 0 →
      (fibre a).Finite ∧ (ellipsePoints (Real.sqrt (1 - 3 * a))).Finite ∧
        (Nat.card (fibre a) : ℝ) =
          (1 / 2) * (divisorSum (1 - 3 * a).toNat : ℝ) -
            (1 / 6) * Nat.card (ellipsePoints (Real.sqrt (1 - 3 * a)))

end CubicTargets.Counting.ExactFormula
