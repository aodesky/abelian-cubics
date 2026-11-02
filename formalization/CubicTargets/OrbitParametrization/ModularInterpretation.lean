import Cubic.OrbitParametrization.C3Algebra
import Cubic.QuadraticCorrespondence.RationalQuotientFunctor
import Cubic.QuadraticCorrespondence.DescendedCoefficients

/-!
# `thm:modularInterpretation`

Rational points of `T` are the rational points of the actual descended quotient
ring. `C₃`-algebras, trace-one normal elements and equivalence of pairs are as in
the paper (`Cubic.OrbitParametrization.C3Algebra`). The claim is a bijection
between rational points and equivalence classes of pairs, compatible with
characteristic polynomials: the point of `(K,x)` has characteristic polynomial
`(t-x)(t-σx)(t-σ²x)`, the characteristic polynomial of `x`. The map is the natural
one: `Φ(K,x)` is the restriction to the quotient of the cover point given by the
unit `u = x[1] + σ²x[σ] + σx[σ²]` of `K[C₃]`.
-/

namespace CubicTargets.OrbitParametrization.ModularInterpretation

open Cubic.OrbitParametrization.C3Algebra
open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Polynomial

def Claim : Prop :=
  ∃ Φ : Pair → (quotientFixedRing →ₐ[ℚ] ℚ),
    Function.Surjective Φ ∧
    (∀ p q : Pair, Φ p = Φ q ↔ Equivalent p q) ∧
    (∀ p : Pair, (characteristicPolynomial (Φ p)).map (algebraMap ℚ p.algebra.carrier) =
      ∏ g : C3, (X - C (p.algebra.act g p.element))) ∧
    ∀ p : Pair, ∃ u : traceOneUnits p.algebra.carrier,
      (u.val : GroupAlgebra p.algebra.carrier) =
        coordinates _ p.element (p.algebra.act (Multiplicative.ofAdd 2) p.element)
          (p.algebra.act (Multiplicative.ofAdd 1) p.element) ∧
      ∀ b, algebraMap ℚ p.algebra.carrier (Φ p b) =
        Cubic.QuadraticCorrespondence.RationalQuotientFunctor.quotientPoint _ u b

end CubicTargets.OrbitParametrization.ModularInterpretation
