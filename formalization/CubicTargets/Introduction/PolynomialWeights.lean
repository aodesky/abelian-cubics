import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Cubic.QuadraticCorrespondence.DescendedCoefficients
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# `eqn:polynomialWeights`

"We prove that the image of this function is the subset of polynomials which either have
Galois group `C₃` or split into three linear factors over `ℚ` with at most two being the
same, and if `f` is such a polynomial, then the number of rational points of `T` with
characteristic polynomial `f` is given by `w_f = 1` if `f` has a double root, `2` otherwise."

* Rational points of `T` are `quotientFixedRing →ₐ[ℚ] ℚ`; the function is
  `characteristicPolynomial`.
* "Galois group `C₃` or split with at most two roots the same" is `Admissible`.
* "`f` has a double root" is taken literally: some complex `r` with `(t − r)² ∣ f`.
  Admissible polynomials have no triple root.
* Finiteness of the counted set is part of the conclusion.
-/

noncomputable section

namespace CubicTargets.Introduction.PolynomialWeights

open Polynomial Cubic.QuadraticCorrespondence
open CorrespondencePolynomials DescendedCoefficients CyclotomicTorusGalois

def HasDoubleRoot (f : ℚ[X]) : Prop :=
  ∃ r : ℂ, (X - C r) ^ 2 ∣ f.map (algebraMap ℚ ℂ)

open scoped Classical in
def Claim : Prop :=
  ∀ a b : ℚ, Admissible (cubic a b) →
    {P : quotientFixedRing →ₐ[ℚ] ℚ | characteristicPolynomial P = cubic a b}.Finite ∧
      Nat.card {P : quotientFixedRing →ₐ[ℚ] ℚ // characteristicPolynomial P = cubic a b} =
        if HasDoubleRoot (cubic a b) then 1 else 2

end CubicTargets.Introduction.PolynomialWeights
