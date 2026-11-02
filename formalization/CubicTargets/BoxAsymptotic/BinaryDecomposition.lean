import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Rademacher–Menchov binary decomposition inequality

Literature input: Montgomery–Vaughan, *Multiplicative Number Theory II:
Primes and Sieves*, author draft, Appendix E.4.3, pp. 356–357, (E.28):
https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf

We use the pointwise inequality preceding its integrated applications, with
ambient length `2^J`. We require the cutoff to be strictly smaller than that
length: the displayed dyadic expansion in the draft does not contain the right
endpoint. Zero cutoff is harmless. The right side here includes all binary
blocks, rather than just the left halves in (E.28), and also permits blocks
beyond the ambient interval; these additions are nonnegative. Applications
will use a sequence supported inside the ambient interval.

This general finite-sequence inequality contains no angular characters, ideal
coefficients, sieve estimate, or moment estimate. It is an explicit hypothesis,
not a Lean axiom.
-/

namespace CubicTargets.BoxAsymptotic.BinaryDecomposition

open scoped BigOperators

def block (j b : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ j * b) (2 ^ j * (b + 1))

def BlackBox : Prop :=
  ∀ (J q : ℕ), q < 2 ^ J → ∀ (f : ℕ → ℂ),
    ‖∑ n ∈ Finset.Icc 1 q, f n‖ ^ 2 ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ∑ b ∈ Finset.range (2 ^ J),
        ‖∑ n ∈ block j b, f n‖ ^ 2

end CubicTargets.BoxAsymptotic.BinaryDecomposition
