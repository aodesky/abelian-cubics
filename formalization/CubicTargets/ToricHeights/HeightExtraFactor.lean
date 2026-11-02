import CubicTargets.ToricHeights.LocalHeightFormula
import Cubic.ToricHeights.AffineInvariantRing
import Cubic.PoissonSummation.AdelicHeightZetaData

/-!
# Concrete statement of `eqn:heightExtraFactor`

In the proof of `prop:canonicalHeight`: when the rational point `P` is `D₀`-integral, the
only contribution to its height with respect to `O(3D₀)` is the local contribution of the
complex place `w` of `E`, which is
```text
max(1, |1-3e₂|², |1 - 9/2 e₂ + 27/2 e₃ + √-27/2 √disc|²)^{1/2}.
```

## Correspondence

* Rational points of `T` are `quotientFixedRing →ₐ[ℚ] ℚ`; `D₀`-integrality is
  `AffineInvariantRing.IntegralPoint` (the paper's definition), as in `prop:canonicalHeight`.
* The height of `O(3D₀)` is `AdelicHeightZetaData.height 3 0` at the diagonal point; its
  finite local factors are `(family p).inverseHeight (-3) 0` and its complex factor is
  `ArchimedeanQuotientLogarithm.inverseHeight (-3) 0` (see `eqn:localHeight`).
* `e₂ = linearCoefficient`, `e₃ = -constantCoefficient`, `√disc = WeightVectors.sqrtDisc`
  evaluated at `P` (rational numbers), and `√-27 = i√27`, the image of the project's
  `3(2ζ+1)` under the complex place (`ζ ↦ e^{2πi/3}`); `|·|` is the complex absolute value.
  `LocalHeightFormula.complexWeightValue (baseChange ℝ P) 1` is exactly
  `1 - 9/2 e₂ + 27/2 e₃ + (i√27)/2 √disc` at the real point of `P`.

The claim records the three assertions of the sentence: every finite factor is one, the
complex factor is the displayed quantity, and hence so is the height.
-/

noncomputable section

namespace CubicTargets.ToricHeights.HeightExtraFactor

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois DescendedCoefficients
open Cubic.ToricHeights Cubic.PoissonSummation
open CubicTargets.ToricHeights.LocalHeightFormula

/-- The displayed complex-place factor for the rational point `P`. -/
def extraFactor (P : quotientFixedRing →ₐ[ℚ] ℚ) : ℝ :=
  (max (max 1 (‖1 - 3 * ((P linearCoefficient : ℚ) : ℂ)‖ ^ 2))
    (‖complexWeightValue (RationalAdelicEmbedding.baseChange ℝ P) 1‖ ^ 2)) ^ (1 / 2 : ℝ)

structure Claim : Prop where
  finite_one : ∀ P : quotientFixedRing →ₐ[ℚ] ℚ, AffineInvariantRing.IntegralPoint P →
    ∀ p : Nat.Primes, (QuotientFiniteFourierProduct.family p).inverseHeight (-3) 0
      (RationalAdelicEmbedding.finiteDiagonal P p) = 1
  complex : ∀ P : quotientFixedRing →ₐ[ℚ] ℚ, AffineInvariantRing.IntegralPoint P →
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 (RationalAdelicEmbedding.baseChange ℝ P) =
      (extraFactor P : ℂ)
  height : ∀ P : quotientFixedRing →ₐ[ℚ] ℚ, AffineInvariantRing.IntegralPoint P →
    AdelicHeightZetaData.height 3 0 (RationalAdelicEmbedding.diagonal P) = (extraFactor P : ℂ)

end CubicTargets.ToricHeights.HeightExtraFactor
