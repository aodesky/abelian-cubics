import Cubic.QuadraticCorrespondence.RationalCorrespondence
import Mathlib.Data.Set.Card

/-!
# Polynomial fibres and the two conjugate quadratic parameters

The inverse quadratic in `prop:cyclotomicParametrization` determines every
fibre of the characteristic-polynomial map. A polynomial in the image has
precisely the point and its conjugate parameter as preimages. That every
admissible polynomial occurs is proved in `QuotientPolynomialConverse`, and the
comparison of separability with distinctness of the parameters in
`QuotientPolynomialMultiplicity`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientPolynomialFibres

open CyclotomicField CyclotomicTorusGalois DescendedCoefficients
open RationalCoefficientFormula RationalCorrespondence CorrespondencePolynomials
open Polynomial

abbrev Points := quotientFixedRing →ₐ[ℚ] ℚ

/-- Conjugation transported through the specified parametrization. -/
def conjugatePoint (p : Points) : Points :=
  parameterEquiv.symm (Units.map conjugation.toMonoidHom (parameterEquiv p))

theorem parameter_conjugate (p : Points) :
    (parameterEquiv (conjugatePoint p) : E) = conjugation (parameterEquiv p : E) := by
  simp [conjugatePoint]

private theorem norm_conjugate (x : E) :
    Algebra.norm ℚ (conjugation x) = Algebra.norm ℚ x := by
  apply (algebraMap ℚ E).injective
  rw [norm_eq_mul_conjugation, norm_eq_mul_conjugation, conjugation_involutive]
  exact mul_comm _ _

private theorem trace_conjugate (x : E) :
    Algebra.trace ℚ E (conjugation x) = Algebra.trace ℚ E x := by
  apply (algebraMap ℚ E).injective
  rw [trace_eq_add_conjugation, trace_eq_add_conjugation, conjugation_involutive]
  exact add_comm _ _

theorem polynomial_conjugate (p : Points) :
    characteristicPolynomial (conjugatePoint p) = characteristicPolynomial p := by
  rw [characteristicPolynomial_eq, characteristicPolynomial_eq,
    parameter_conjugate, norm_conjugate, trace_conjugate]

/-- The points with the same polynomial as `p` are `p` and its conjugate. -/
theorem polynomial_eq_iff (p q : Points) :
    characteristicPolynomial q = characteristicPolynomial p ↔
      q = p ∨ q = conjugatePoint p := by
  constructor
  · intro h
    have hroot := inverse_quadratic (p linearCoefficient) (p constantCoefficient) q h
    rw [inverseQuadratic_eq] at hroot
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      trace_eq_add_conjugation, norm_eq_mul_conjugation] at hroot
    have hz : ((parameterEquiv q : E) - (parameterEquiv p : E)) *
        ((parameterEquiv q : E) - conjugation (parameterEquiv p : E)) = 0 := by
      linear_combination hroot
    rcases mul_eq_zero.mp hz with hq | hq
    · exact Or.inl (parameterEquiv.injective (Units.ext (sub_eq_zero.mp hq)))
    · right
      apply parameterEquiv.injective
      apply Units.ext
      rw [parameter_conjugate]
      exact sub_eq_zero.mp hq
  · rintro (rfl | rfl)
    · rfl
    · exact polynomial_conjugate p

theorem fibre_eq_pair (p : Points) :
    {q : Points | characteristicPolynomial q = characteristicPolynomial p} =
      {p, conjugatePoint p} := by
  ext q
  simp only [Set.mem_setOf_eq, polynomial_eq_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every polynomial has a finite fibre. -/
theorem finite_fibre (f : ℚ[X]) : {q : Points | characteristicPolynomial q = f}.Finite := by
  classical
  by_cases h : ∃ p : Points, characteristicPolynomial p = f
  · obtain ⟨p, rfl⟩ := h
    rw [fibre_eq_pair]
    exact (Set.finite_singleton _).insert _
  · have he : {q : Points | characteristicPolynomial q = f} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hq => h ⟨q, hq⟩
    rw [he]
    exact Set.finite_empty

theorem fibre_card_two (p : Points) (h : p ≠ conjugatePoint p) :
    Nat.card {q : Points // characteristicPolynomial q = characteristicPolynomial p} = 2 := by
  change ({q : Points | characteristicPolynomial q = characteristicPolynomial p} : Set Points).ncard = 2
  rw [fibre_eq_pair]
  exact Set.ncard_pair h

theorem fibre_card_one (p : Points) (h : p = conjugatePoint p) :
    Nat.card {q : Points // characteristicPolynomial q = characteristicPolynomial p} = 1 := by
  change ({q : Points | characteristicPolynomial q = characteristicPolynomial p} : Set Points).ncard = 1
  rw [fibre_eq_pair, ← h]
  simp

end Cubic.QuadraticCorrespondence.QuotientPolynomialFibres
