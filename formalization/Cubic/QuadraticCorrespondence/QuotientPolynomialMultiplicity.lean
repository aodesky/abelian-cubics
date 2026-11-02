import Cubic.QuadraticCorrespondence.QuotientPolynomialFibres
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Exact multiplicities for polynomials in the quotient-point image

The two roots of the inverse quadratic coincide exactly when the cubic has
a repeated root. Together with the fibre description, this gives the
paper's multiplicities two and one for every polynomial in the image.
That every admissible polynomial occurs is proved in `QuotientPolynomialConverse`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientPolynomialMultiplicity

open CyclotomicField DescendedCoefficients RationalCoefficientFormula
open QuotientPolynomialFibres Polynomial

/-- The discriminant in terms of the two conjugate quadratic parameters. -/
theorem discriminant_formula (p : Points) :
    algebraMap ℚ E (⟨1, -1, p linearCoefficient, p constantCoefficient⟩ : Cubic ℚ).discr =
      -((parameterEquiv p : E) * conjugation (parameterEquiv p : E)) ^ 2 *
        ((parameterEquiv p : E) - conjugation (parameterEquiv p : E)) ^ 2 / 27 := by
  rw [linearCoefficient_eq, constantCoefficient_eq]
  simp only [Cubic.discr, map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat,
    map_div₀, norm_eq_mul_conjugation, trace_eq_add_conjugation]
  ring

theorem discriminant_ne_zero_iff (p : Points) :
    (⟨1, -1, p linearCoefficient, p constantCoefficient⟩ : Cubic ℚ).discr ≠ 0 ↔
      p ≠ conjugatePoint p := by
  have hconj : conjugation (parameterEquiv p : E) ≠ 0 :=
    (_root_.map_ne_zero conjugation).mpr (parameterEquiv p).ne_zero
  have heq : p = conjugatePoint p ↔
      (parameterEquiv p : E) = conjugation (parameterEquiv p : E) := by
    rw [← parameter_conjugate]
    exact parameterEquiv.injective.eq_iff.symm.trans Units.val_injective.eq_iff.symm
  rw [← _root_.map_ne_zero (algebraMap ℚ E), discriminant_formula]
  simp only [ne_eq, heq]
  simp [(parameterEquiv p).ne_zero, hconj, sub_eq_zero]

/-- Separability of the cubic in terms of the two parameters. -/
theorem separable_iff (p : Points) :
    (characteristicPolynomial p).Separable ↔ p ≠ conjugatePoint p := by
  let Q : Cubic ℚ := ⟨1, -1, p linearCoefficient, p constantCoefficient⟩
  have hQ : Q.a ≠ 0 := by norm_num [Q]
  have hpoly : Q.toPoly = characteristicPolynomial p := by
    simp [Q, Cubic.toPoly, characteristicPolynomial, CorrespondencePolynomials.cubic,
      sub_eq_add_neg]
  have hn : characteristicPolynomial p ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ[X] => f.coeff 3) h
    norm_num [characteristicPolynomial] at hc
  have hs := IsAlgClosed.splits ((characteristicPolynomial p).map
    (algebraMap ℚ (AlgebraicClosure ℚ)))
  have hd := Cubic.discr_ne_zero_iff_roots_nodup hQ
    (show (Q.toPoly.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits by rw [hpoly]; exact hs)
  rw [← discriminant_ne_zero_iff]
  symm
  apply hd.trans
  rw [Cubic.roots, Cubic.map_toPoly]
  rw [hpoly, nodup_roots_iff_of_splits (map_ne_zero hn) hs, separable_map]

theorem separable_fibre_card (p : Points) (hp : (characteristicPolynomial p).Separable) :
    Nat.card {q : Points // characteristicPolynomial q = characteristicPolynomial p} = 2 :=
  fibre_card_two p ((separable_iff p).mp hp)

theorem repeated_fibre_card (p : Points) (hp : ¬ (characteristicPolynomial p).Separable) :
    Nat.card {q : Points // characteristicPolynomial q = characteristicPolynomial p} = 1 := by
  apply fibre_card_one
  simpa only [separable_iff, not_not] using hp

end Cubic.QuadraticCorrespondence.QuotientPolynomialMultiplicity
