import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The cited additive large sieve

H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20 (1973),
119–134, Theorem 1, with its dual form explicitly displayed in (2.3), p. 122.
Source inspected: https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf

The source uses the minimum spacing modulo one. Here `δ` is any positive lower
bound for that spacing, and `(M,M+N]` is indexed by `Fin N`. This only enlarges
the right side. Empty and singleton point sets satisfy the same inequality.

This is an explicit literature hypothesis, not an axiom. In particular it does
not assume the paper's angular large sieve or its maximum over norm cutoffs.
-/

namespace CubicTargets.BoxAsymptotic.AdditiveLargeSieve

open scoped BigOperators

/-- Montgomery–Vaughan's dual additive large sieve, with `e(x)=exp(2πix)`. -/
def BlackBox : Prop :=
  ∀ (R N : ℕ), 0 < N → ∀ (M : ℤ) (θ : Fin R → ℝ) (c : Fin R → ℂ) (δ : ℝ),
    0 < δ → (∀ r s : Fin R, r ≠ s → ∀ m : ℤ, δ ≤ |θ r - θ s - m|) →
    (∑ n : Fin N, ‖∑ r : Fin R, c r *
      Complex.exp ((2 * Real.pi * (M + (n : ℤ) + 1) * θ r : ℝ) * Complex.I)‖ ^ 2) ≤
        ((N : ℝ) + δ⁻¹) * ∑ r : Fin R, ‖c r‖ ^ 2

end CubicTargets.BoxAsymptotic.AdditiveLargeSieve
