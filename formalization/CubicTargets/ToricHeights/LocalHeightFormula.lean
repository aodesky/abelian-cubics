import Cubic.ToricHeights.WeightVectors
import Cubic.ToricHeights.QuotientFiniteHeight
import Cubic.ToricHeights.ArchimedeanQuotientLogarithm

/-!
# Concrete statement of `eqn:localHeight`

In the proof of `prop:canonicalHeight`: the local toric height `H_w` with respect to
`O(3D₀)` of a point of `T` is
```text
max(1, |1-3e₂|_w, |z₋|_w, |z₊|_w)^{1/[E:ℚ]},   z± = 1 - 9/2 e₂ + 27/2 e₃ ± √-27/2 √disc,
```
with `|·|_w = q_w^{-ord_w(·)}` at finite `w` and `|·|_w = |·|^{d_w}` (`d_w = 2`) at the
complex place.

## Correspondence

* Points of `T` over `ℚ_v` are the original quotient points `quotientFixedRing →ₐ[ℚ] ℚ_v`
  (`ℚ_∞ = ℝ`). The claim is stated for **every** such local point (not only rational
  points), at every place `w` of `E`: both places over a split prime (`place`, `secondPlace`),
  the inert place, the ramified place over `3`, and the complex place.
* The local factor of the height of `O(3D₀)` is the project's factor
  `q_w^{φ(ℓ_w(x))/[E:ℚ]}` of the inverse height at parameters `(s₀,σ)=(-3,0)`
  (`H(x,s) = H^{-1}(x,-s)`; `supportFunction (-3) 0 = -φ_{3D₀}`), i.e.
  `(q_w^{-φ_{3D₀}(ℓ_w(x))})^{1/[E:ℚ]}` as in the paper's definition of `H`.
  At a split prime the project's `splitInverseHeight p (-3) 0 P` is by definition the product
  of the two place factors stated separately here; at the inert and ramified primes and at
  infinity the factor is the project's `inertInverseHeight`, `ramifiedInverseHeight` and
  `ArchimedeanQuotientLogarithm.inverseHeight`.
* `q_w` is the cardinality of the residue field of the actual local integer ring, and
  `ord_w` is the normalized valuation of `E_w` used to define `ℓ_w`
  (`PadicMultiplicative.valuation`, `InertLocalModel.integerValuation`,
  `RamifiedLocalModel.integerValuation`).
* `e₂ = linearCoefficient`, `e₃ = -constantCoefficient` (the project's cubic is
  `t³ - t² + e₂ t - e₃`), `√disc = (X-Z)(Y-X)(Z-Y)` is `WeightVectors.sqrtDisc`, and
  `√-27 = 3(2ζ+1)` is `WeightVectors.sqrtNegTwentySeven` (the TeX does not fix the sign of
  `√-27`; at the complex place, where `ζ ↦ e^{2πi/3}`, it is `i√27`). Global functions are
  mapped into `E_w` by the place: `f ↦ place (1 ⊗ P f)` and `√-27 ↦ place (√-27 ⊗ 1)`.
* `|y|_w = q_w^{-ord_w(y)}` needs `y ≠ 0`; the claim asserts that `1-3e₂` and `z±` are nonzero
  at every local point.
-/

noncomputable section

namespace CubicTargets.ToricHeights.LocalHeightFormula

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois DescendedCoefficients
open Cubic.ToricHeights

section Local

variable {A : Type*} [CommRing A] [Algebra ℚ A] {L : Type*} [Field L]
variable (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A)

/-- A global function evaluated at `P` and mapped into `E_w`. -/
def value (f : quotientFixedRing) : L := place ((1 : E) ⊗ₜ[ℚ] P f)

/-- The image of `√-27 = 3(2ζ+1)` in `E_w`. -/
def sqrtNegTwentySeven : L := place (WeightVectors.sqrtNegTwentySeven ⊗ₜ[ℚ] (1 : A))

/-- `1 - 3e₂`. -/
def normValue : L := 1 - 3 * value place P linearCoefficient

/-- `z± = 1 - 9/2 e₂ + 27/2 e₃ ± √-27/2 √disc`, with `e₃ = -constantCoefficient`. -/
def weightValue (sign : ℤ) : L :=
  1 - 9 / 2 * value place P linearCoefficient + 27 / 2 * (-value place P constantCoefficient) +
    (sign : L) * (sqrtNegTwentySeven place / 2) * value place P WeightVectors.sqrtDisc

/-- `|y|_w = q_w^{-ord_w(y)}` for `y ≠ 0`. -/
def wAbs (q : ℕ) (ord : Lˣ →* Multiplicative ℤ) (y : L) (hy : y ≠ 0) : ℝ :=
  (q : ℝ) ^ (-((ord (Units.mk0 y hy)).toAdd : ℝ))

/-- `eqn:localHeight` at a finite place `w` with residue cardinality `q` and valuation `ord`:
the three values are nonzero and `factor = max(1,|1-3e₂|_w,|z₋|_w,|z₊|_w)^{1/[E:ℚ]}`. -/
def FiniteFormula (q : ℕ) (ord : Lˣ →* Multiplicative ℤ) (factor : ℂ) : Prop :=
  ∃ (hN : normValue place P ≠ 0) (hm : weightValue place P (-1) ≠ 0)
    (hp : weightValue place P 1 ≠ 0),
    factor = ((max (max 1 (wAbs q ord _ hN))
      (max (wAbs q ord _ hm) (wAbs q ord _ hp))) ^ (1 / (Module.finrank ℚ E : ℝ)) : ℝ)

end Local

/-- `z±` at the complex place, for a real point `P`: `1 - 9/2 e₂ + 27/2 e₃ ± (i√27)/2 √disc`. -/
def complexWeightValue (P : quotientFixedRing →ₐ[ℚ] ℝ) (sign : ℤ) : ℂ :=
  1 - 9 / 2 * (P linearCoefficient : ℂ) + 27 / 2 * (-(P constantCoefficient : ℂ)) +
    (sign : ℂ) * (Complex.I * Real.sqrt 27 / 2) * (P WeightVectors.sqrtDisc : ℂ)

/-- The split-place factor `q_w^{φ_{(-3,0)}(ℓ_w(P))/[E:ℚ]}` at a place with local cocharacter `n`. -/
def splitFactor (p : ℕ) [Fact p.Prime] (n : ℝ × ℝ) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^
    (supportFunction (-3) 0 n / Module.finrank ℚ E)

structure Claim : Prop where
  split_first : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    FiniteFormula (SplitQuotientLogarithm.place p) P
      (Nat.card (IsLocalRing.ResidueField ℤ_[p])) (Cubic.OrbitParametrization.PadicMultiplicative.valuation p)
      (splitFactor p (QuotientFiniteHeight.splitCoordinates p P))
  split_second : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    FiniteFormula (SplitQuotientLogarithm.secondPlace p) P
      (Nat.card (IsLocalRing.ResidueField ℤ_[p])) (Cubic.OrbitParametrization.PadicMultiplicative.valuation p)
      (splitFactor p (QuotientFiniteHeight.splitSecondCoordinates p P))
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    FiniteFormula (InertQuotientLogarithm.place p).toRingHom P
      (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)))
      (InertLocalModel.integerValuation p)
      (QuotientFiniteHeight.inertInverseHeight p (-3) 0 P)
  ramified : ∀ P : quotientFixedRing →ₐ[ℚ] ℚ_[3],
    FiniteFormula RamifiedQuotientLogarithm.place.toRingHom P
      (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers))
      RamifiedLocalModel.integerValuation
      (QuotientFiniteHeight.ramifiedInverseHeight (-3) 0 P)
  complex : ∀ P : quotientFixedRing →ₐ[ℚ] ℝ,
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 P =
      ((max (max 1 (‖1 - 3 * (P linearCoefficient : ℂ)‖ ^ 2))
        (max (‖complexWeightValue P (-1)‖ ^ 2) (‖complexWeightValue P 1‖ ^ 2))) ^
          (1 / (Module.finrank ℚ E : ℝ)) : ℝ)

end CubicTargets.ToricHeights.LocalHeightFormula
