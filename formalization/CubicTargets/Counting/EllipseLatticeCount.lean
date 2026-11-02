import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lattice points in the filled ellipse `E_H°`

Target for `eqn:ellipseLatticeCount` in `lemma:reducibles`.
The ellipse `E_H` of `thm:exactFormula` is `x² + y² + xy - x - y = (H² - 1)/3`,
and `E_H°` is the closed region it bounds. The claim is that `E_H° ∩ ℤ²` is
finite for `H ≥ 1` and that
`#(E_H° ∩ ℤ²) = (2π/(3√3)) H² + O(H)` for `H ≥ 1`.
-/

namespace CubicTargets.Counting.EllipseLatticeCount

/-- The integer points of the closed filled ellipse `E_H°`. -/
def latticePoints (H : ℝ) : Set (ℤ × ℤ) :=
  {p | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) - p.1 - p.2 ≤ (H ^ 2 - 1) / 3}

def Claim : Prop :=
  (∀ H : ℝ, 1 ≤ H → (latticePoints H).Finite) ∧
    ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
      |(Nat.card (latticePoints H) : ℝ) - 2 * Real.pi / (3 * Real.sqrt 3) * H ^ 2| ≤ K * H

end CubicTargets.Counting.EllipseLatticeCount
