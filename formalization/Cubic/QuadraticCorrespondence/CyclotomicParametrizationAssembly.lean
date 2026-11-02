import Cubic.QuadraticCorrespondence.CyclotomicParametrization
import Cubic.QuadraticCorrespondence.RationalCorrespondence
import Cubic.QuadraticCorrespondence.QuotientCubicClassification
import Cubic.QuadraticCorrespondence.QuotientPolynomialConverse
import Cubic.QuadraticCorrespondence.QuotientPolynomialFibres
import Cubic.ToricHeights.CanonicalHeight
import CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete

/-!
# Proof of `prop:cyclotomicParametrization`

Assembly of the proposition's clauses with the canonical geometric data:

* the specified isomorphism of point functors and its canonicity up to automorphisms
  of the group functor (`CyclotomicParametrization`);
* the coefficient formula through the norm and trace (`RationalCoefficientFormula`);
* the toric height of an integral point, via `prop:canonicalHeight`, and its agreement
  with the square root of the norm (`RationalCorrespondence`);
* the forward classification, the converse and the fibre counts
  (`QuotientCubicClassification`, `QuotientPolynomialConverse`);
* the inverse quadratic and the integrality criterion (`RationalCorrespondence`).
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicParametrizationAssembly

open CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
open CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete
open Cubic.QuadraticCorrespondence.CyclotomicParametrization

/-- The canonical toric height of an integral point is `√(1 − 3a)`. -/
theorem height_eq (p : Points ℚ) (hp : p ∈ canonicalGeometry.integralLocus) :
    canonicalGeometry.height p =
      Real.sqrt (1 - 3 * (p DescendedCoefficients.linearCoefficient : ℝ)) := by
  change (Cubic.PoissonSummation.AdelicHeightZetaData.height 1 0
    (Cubic.PoissonSummation.RationalAdelicEmbedding.diagonal p)).re = _
  rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 p hp, Complex.ofReal_re]

open Polynomial CyclotomicField CorrespondencePolynomials RationalCoefficientFormula in
/-- Every root of `g` in `E` is the element of a point over `f`: if `p` lies over `f` with
element `x`, then `g = (t − x)(t − x̄)`, and `x̄` is the element of the conjugate point. -/
theorem quadratic_roots :
    CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete.QuadraticRoots := by
  intro a b h β hβ
  obtain ⟨p, hp⟩ := QuotientPolynomialConverse.exists_point h
  obtain ⟨ha, hb⟩ := cubic_eq_iff.mp (show cubic (p DescendedCoefficients.linearCoefficient)
    (p DescendedCoefficients.constantCoefficient) = cubic a b from hp)
  rw [← ha, ← hb, RationalCorrespondence.inverseQuadratic_eq] at hβ
  set x : E := (parameterEquiv p : E)
  have hN := norm_eq_mul_conjugation x
  have hT := trace_eq_add_conjugation x
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hβ
  rw [hN, hT] at hβ
  have hfac : (β - x) * (β - conjugation x) = 0 := by linear_combination hβ
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact ⟨p, hp, (sub_eq_zero.mp h1).symm⟩
  · refine ⟨QuotientPolynomialFibres.conjugatePoint p, ?_, ?_⟩
    · exact (QuotientPolynomialFibres.polynomial_conjugate p).trans hp
    · rw [QuotientPolynomialFibres.parameter_conjugate]; exact (sub_eq_zero.mp h1).symm

theorem «prop:cyclotomicParametrization» :
    CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete.Claim := by
  refine ⟨⟨specifiedIsomorphism, ?_⟩, quadratic_roots⟩
  exact {
    specified_isomorphism := fun A _ _ p => rfl
    canonical_up_to_automorphism := fun κ => canonical_up_to_automorphism specifiedIsomorphism κ
    coefficient_formula := fun p => RationalCoefficientFormula.characteristicPolynomial_eq p
    height_coefficient := height_eq
    height_norm := fun p hp => by
      rw [height_eq p hp]
      exact RationalCorrespondence.sqrt_coefficient_eq_sqrt_norm p
    image_admissible := QuotientCubicClassification.claim
    converse := fun a b h => QuotientPolynomialConverse.exists_point h
    finite_fibres := fun a b _ => QuotientPolynomialConverse.finite_fibre
    separable_fibre_card := fun a b h hs => QuotientPolynomialConverse.separable_fibre_card h hs
    repeated_fibre_card := fun a b h hs => QuotientPolynomialConverse.repeated_fibre_card h hs
    inverse_denominator_ne_zero := RationalCoefficientFormula.inverse_denominator_ne_zero
    inverse_quadratic := RationalCorrespondence.inverse_quadratic
    integrality_iff := RationalCorrespondence.integrality_iff }

end Cubic.QuadraticCorrespondence.CyclotomicParametrizationAssembly
