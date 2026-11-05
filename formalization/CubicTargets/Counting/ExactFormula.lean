import Cubic.Counting.PolynomialCountData
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# `thm:exactFormula`

"For `m ≥ 1` let `a_E(m)` denote the number of ideals of norm `m` in the ring of integers
`𝓞_E` of `E`. If `t³−t²+at+b ∈ ℤ[t]` has Galois group `C₃`, then `a ≤ 0`. Fix
`a ∈ ℤ_{≤0}` and put `n = 1−3a`. The number of polynomials of the form `t³−t²+at+b ∈ ℤ[t]`
with Galois group `C₃` is equal to `(a_E(n³) − a_E(n))/2`."

* `E = ℚ(ζ₃)` is Mathlib's `CyclotomicField 3 ℚ`, and `a_E(m)` counts ideals of
  `𝓞 E` of absolute norm `m`.
* `F` is `PolynomialCountData.cyclicPolynomials`. The polynomials with linear
  coefficient `a` are counted through `b ↦ t³−t²+at+b`, which is injective.
* Finiteness of the counted set of polynomials and of both sets of ideals is part of the
  conclusion, so `Nat.card` cannot hide an infinite set.
-/

noncomputable section

namespace CubicTargets.Counting.ExactFormula

open Cubic.Counting.PolynomialCountData NumberField

/-- The ideals of `𝓞_E`, `E = ℚ(ζ₃)`, of absolute norm `m`. -/
def normIdeals (m : ℕ) : Set (Ideal (𝓞 (CyclotomicField 3 ℚ))) := {I | Ideal.absNorm I = m}

/-- `a_E(m)`. -/
def aE (m : ℕ) : ℕ := Nat.card (normIdeals m)

/-- The `b` with `t³−t²+at+b ∈ F`. -/
def fibre (a : ℤ) : Set ℤ := {b | traceOneCubic a b ∈ cyclicPolynomials}

def Claim : Prop :=
  (∀ a b : ℤ, traceOneCubic a b ∈ cyclicPolynomials → a ≤ 0) ∧
    ∀ a : ℤ, a ≤ 0 →
      (fibre a).Finite ∧ (normIdeals (1 - 3 * a).toNat).Finite ∧
        (normIdeals ((1 - 3 * a).toNat ^ 3)).Finite ∧
        (Nat.card (fibre a) : ℝ) =
          ((aE ((1 - 3 * a).toNat ^ 3) : ℝ) - aE (1 - 3 * a).toNat) / 2

end CubicTargets.Counting.ExactFormula
