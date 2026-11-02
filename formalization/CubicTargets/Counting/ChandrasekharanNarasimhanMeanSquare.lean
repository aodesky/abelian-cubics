import Cubic.Counting.HeightCoefficientData
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Chandrasekharan–Narasimhan, *The approximate functional equation for a class
of zeta-functions*, Math. Ann. 152 (1963), 30–64, Theorem 4, equation (80),
p. 63. For a number field of degree `n`, their normalized mean
`M(σ,T) = (1/T) ∫₁ᵀ |ζ_K(σ+it)|² dt` (p. 55) satisfies
`M(σ,T) = O(T^(n(1-σ)-1) log^n T)` for `1/n ≤ σ ≤ 1-1/n`.
Here `n = 2`, `σ = 1/2`, and `K = ℚ(√-3)`, whose continued Dedekind
zeta function is the established `zetaE = ζ L(χ₋₃,·)`.

This explicit hypothesis asserts only the eventual upper bound at the
critical line. Removing the normalization and extending to every `T ≥ 2`
are proved in `CriticalMeanSquare.lean`. No axiom is introduced.
-/

namespace CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare
open Cubic.Counting.HeightCoefficientData Filter

def BlackBox : Prop := ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
  (1 / T) * (∫ t in (1 : ℝ)..T, ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
    C * (Real.log T) ^ 2

end CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare
