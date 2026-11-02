import Cubic.Introduction.EisensteinPointData
import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Cubic.QuadraticCorrespondence.QuotientPolynomialFibres

namespace CubicTargets.Introduction.IdealParametrization

open Cubic.Introduction.EisensteinPointData
open Cubic.QuadraticCorrespondence CyclotomicField
open Cubic.PoissonSummation.CyclotomicIntegerUnits

/-- The arithmetic assertions in the introductory ideal remark.
The separately cited sharper estimate is recorded with its literature input. -/
structure Claim : Prop where
  parametrization : ∃ e : IntegralTorus ≃ PrimaryCubes,
    (∀ P, ((e P).1 : E) = pointResolvent P.1) ∧
    (∀ P, (Algebra.norm ℚ ((e P : PrimaryCubes).1 : E) : ℝ) = pointHeight P ^ 6) ∧
    (∀ P, CorrespondencePolynomials.HasCyclicCubicGaloisGroup
      (DescendedCoefficients.characteristicPolynomial P.1) ↔
        ¬ ∃ r : E, r ^ 3 = ((e P : PrimaryCubes).1 : E))
  fullAffine : ∃ e : IntegralAffine ≃ IntegralTorus,
    ∀ P, Cubic.ToricHeights.AffinePointComparison.restrictPoint (e P).1 = P.1
  ideals : ∃ e : PrimaryCubes ≃ CubeIdeals,
    ∀ β, (e β).1 = Ideal.span {β.1}
  idealCondition : ∀ I : Ideal Integers,
    (¬ 3 ∣ Ideal.absNorm I) ↔
      I ⊔ Ideal.span {(3 : Integers)} = ⊤
  polynomialFibres : ∀ P Q : IntegralTorus,
    DescendedCoefficients.characteristicPolynomial P.1 =
      DescendedCoefficients.characteristicPolynomial Q.1 ↔
    pointResolvent Q.1 = pointResolvent P.1 ∨
      pointResolvent Q.1 = conjugation (pointResolvent P.1)
  polynomialImage : ∀ a b : ℤ,
    CorrespondencePolynomials.HasCyclicCubicGaloisGroup
      (CorrespondencePolynomials.cubic a b) →
    ∃ P : IntegralTorus,
      DescendedCoefficients.characteristicPolynomial P.1 =
        CorrespondencePolynomials.cubic a b
  pointSeries_absolute : ∀ s : ℂ, 2 < s.re →
    Summable (fun P : IntegralTorus => ‖(pointHeight P : ℂ) ^ (-s)‖)
  idealSeries_absolute : ∀ s : ℂ, 2 < s.re →
    Summable (fun J : CubeIdeals => ‖(Ideal.absNorm J.1 : ℂ) ^ (-s / 6)‖)
  series : ∀ s : ℂ, 2 < s.re →
    (∑' P : IntegralTorus, (pointHeight P : ℂ) ^ (-s)) =
      ∑' J : CubeIdeals, (Ideal.absNorm J.1 : ℂ) ^ (-s / 6)

end CubicTargets.Introduction.IdealParametrization
