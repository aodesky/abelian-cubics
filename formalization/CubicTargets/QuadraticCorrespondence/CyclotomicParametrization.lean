import Cubic.QuadraticCorrespondence.RationalQuotientGroup
import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Cubic.QuadraticCorrespondence.DescendedCoefficients
import Cubic.QuadraticCorrespondence.CyclotomicCoefficients
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Statement schema for `prop:cyclotomicParametrization`

The conclusions of the proposition, parameterized by the geometric data `Geometry`
(the `D₀`-integral rational locus and the toric height). The concrete statement, with
this data fixed, is `CyclotomicParametrizationConcrete.Claim`; it is proved by
`Cubic.QuadraticCorrespondence.CyclotomicParametrizationAssembly.«prop:cyclotomicParametrization»`.

The point sets are those of the descended cyclic invariant coordinate ring, with
the group law obtained by descent of the invariant-ring coproduct. The coefficient
functions are constructed from the universal cover and proved to descend in
`DescendedCoefficients`.

An algebraic-group isomorphism is expressed by natural group isomorphisms on
points over all commutative rational coefficient algebras. The specified
isomorphism has the quotient-character coordinates.
The Galois, fibre, inverse-quadratic, height and integrality clauses are all
included. There is no hypothesis that rational quotient points lift to the cover.
-/

noncomputable section

namespace CubicTargets.QuadraticCorrespondence.CyclotomicParametrization

open scoped TensorProduct Cubic.QuadraticCorrespondence.RationalQuotientGroup
open Cubic.QuadraticCorrespondence
open CyclotomicField CyclotomicTorusGalois CyclotomicRestrictionScalars
open CorrespondencePolynomials CyclotomicCoefficients
open Polynomial

/-- The concrete invariant-ring point functor with its descended group law. -/
abbrev Points (A : Type) [CommRing A] [Algebra ℚ A] := quotientFixedRing →ₐ[ℚ] A

/-- The geometric data of the proposition. None of its conclusions is assumed here;
the concrete data are fixed in `CyclotomicParametrizationConcrete`. -/
structure Geometry where
  /-- The `D₀`-integral rational locus. -/
  integralLocus : Set (Points ℚ)
  /-- The paper's canonical toric height on rational points. -/
  height : Points ℚ → ℝ

/-- Isomorphism of the represented group functors, with naturality in the coefficient algebra. -/
structure NaturalGroupIso where
  app : (A : Type) → [CommRing A] → [Algebra ℚ A] →
    Points A ≃* (E ⊗[ℚ] A)ˣ
  naturality : ∀ (A B : Type) [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (p : Points A),
    app B (φ.comp p) = Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom (app A p)

/-- Automorphisms of the entire restriction-of-scalars group functor,
not arbitrary automorphisms of its rational point group. -/
structure NaturalUnitAutomorphism where
  app : (A : Type) → [CommRing A] → [Algebra ℚ A] → (E ⊗[ℚ] A)ˣ ≃* (E ⊗[ℚ] A)ˣ
  naturality : ∀ (A B : Type) [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (u : (E ⊗[ℚ] A)ˣ),
    app B (Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom u) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom (app A u)

/-- The rational point map into the unit group of the quadratic field `E`. -/
def rationalEquiv (ι : NaturalGroupIso) : Points ℚ ≃* Eˣ :=
  (ι.app ℚ).trans (Units.mapEquiv (Algebra.TensorProduct.rid ℚ E E).toMulEquiv)

/-- The cubic uses the descended elementary symmetric functions. -/
abbrev characteristicPolynomial := DescendedCoefficients.characteristicPolynomial

/-- The complete conclusions, relative to a specified algebraic-group isomorphism. -/
structure Conclusions (D : Geometry) (ι : NaturalGroupIso) : Prop where
  specified_isomorphism : ∀ (A : Type) [CommRing A] [Algebra ℚ A] (p : Points A),
    ι.app A p = quotientRestrictionScalarsEquiv A p
  canonical_up_to_automorphism : ∀ κ : NaturalGroupIso, ∃ α : NaturalUnitAutomorphism,
    ∀ (A : Type) [CommRing A] [Algebra ℚ A] (p : Points A), κ.app A p = α.app A (ι.app A p)
  coefficient_formula : ∀ p : Points ℚ,
    characteristicPolynomial p =
      cubic ((1 - Algebra.norm ℚ (rationalEquiv ι p : E)) / 3)
        ((Algebra.norm ℚ (rationalEquiv ι p : E) *
          (3 - Algebra.trace ℚ E (rationalEquiv ι p : E)) - 1) / 27)
  height_coefficient : ∀ p ∈ D.integralLocus,
    D.height p = Real.sqrt (1 - 3 * (p DescendedCoefficients.linearCoefficient : ℝ))
  height_norm : ∀ p ∈ D.integralLocus,
    D.height p = Real.sqrt (Algebra.norm ℚ (rationalEquiv ι p : E) : ℝ)
  image_admissible : ∀ p : Points ℚ, Admissible (characteristicPolynomial p)
  converse : ∀ a b : ℚ, Admissible (cubic a b) →
    ∃ p : Points ℚ, characteristicPolynomial p = cubic a b
  finite_fibres : ∀ a b : ℚ, Admissible (cubic a b) →
    Set.Finite {p : Points ℚ | characteristicPolynomial p = cubic a b}
  separable_fibre_card : ∀ a b : ℚ, Admissible (cubic a b) → (cubic a b).Separable →
    Nat.card {p : Points ℚ // characteristicPolynomial p = cubic a b} = 2
  repeated_fibre_card : ∀ a b : ℚ, Admissible (cubic a b) → ¬ (cubic a b).Separable →
    Nat.card {p : Points ℚ // characteristicPolynomial p = cubic a b} = 1
  inverse_denominator_ne_zero : ∀ p : Points ℚ, 1 - 3 * p DescendedCoefficients.linearCoefficient ≠ 0
  inverse_quadratic : ∀ (a b : ℚ) (p : Points ℚ), characteristicPolynomial p = cubic a b →
    Polynomial.eval (rationalEquiv ι p : E) ((inverseQuadratic a b).map (algebraMap ℚ E)) = 0
  integrality_iff : ∀ (p : Points ℚ) (u v : ℚ),
    (rationalEquiv ι p : E) = algebraMap ℚ E u + algebraMap ℚ E v * zeta →
    (HasIntegralCoefficients (characteristicPolynomial p) ↔
      (∃ m : ℤ, normForm u v = 1 + 3 * (m : ℚ)) ∧
      (∃ n : ℤ, normForm u v * (3 - traceForm u v) = 1 + 27 * (n : ℚ)))

/-- The full proposition, parameterized by the geometric data. -/
def Claim (D : Geometry) : Prop := ∃ ι : NaturalGroupIso, Conclusions D ι

end CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
