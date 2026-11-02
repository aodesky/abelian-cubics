import Cubic.QuadraticCorrespondence.DescendedCoefficients
import Cubic.QuadraticCorrespondence.CyclotomicNormTrace

/-!
# Coefficient formulas on every rational quotient point

Use scalar extension of the descended coefficient functions to prove the
paper's norm/trace formulas on all rational points of the invariant ring.
No lift to a rational point of the original cover is assumed.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalCoefficientFormula

open scoped Polynomial TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicRestrictionScalars CyclotomicPointDescent
open SplitLaurentInvariants SplitLaurentPoints SplitLaurentEvaluation DescendedCoefficients

/-- The rational specialization of the specified quotient-character parametrization. -/
def parameterEquiv : (quotientFixedRing →ₐ[ℚ] ℚ) ≃ Eˣ :=
  (quotientRestrictionScalarsEquiv ℚ).trans
    (Units.mapEquiv (Algebra.TensorProduct.rid ℚ E E).toMulEquiv).toEquiv

/-- Scalar extension of a rational quotient point in the quotient Laurent coordinates. -/
def splitEvaluation (p : quotientFixedRing →ₐ[ℚ] ℚ) : CoverRing →ₐ[E] E :=
  (Algebra.TensorProduct.rid ℚ E E).toAlgHom.comp
    (extendPoint (p.comp fixedRingEquiv.toAlgHom))

theorem splitEvaluation_fixed (p : quotientFixedRing →ₐ[ℚ] ℚ) (b : coverFixedRing) :
    splitEvaluation p (b : CoverRing) = algebraMap ℚ E (p (fixedRingEquiv b)) := by
  simp [splitEvaluation, extendPoint_fixed, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

private theorem rid_conjugation (x : E ⊗[ℚ] ℚ) :
    Algebra.TensorProduct.rid ℚ E E (baseChangeConjugation ℚ x) =
      conjugation (Algebra.TensorProduct.rid ℚ E E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c r =>
    change r • conjugation c = conjugation (r • c)
    simp only [Algebra.smul_def, map_mul, conjugation.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem splitEvaluation_conjugation (p : quotientFixedRing →ₐ[ℚ] ℚ) (b : CoverRing) :
    splitEvaluation p (SplitLaurentGalois.conjugate conjugation b) =
      conjugation (splitEvaluation p b) := by
  change Algebra.TensorProduct.rid ℚ E E
    (extendPoint (p.comp fixedRingEquiv.toAlgHom) (SplitLaurentGalois.conjugate conjugation b)) = _
  rw [extendPoint_conjugate, rid_conjugation]
  rfl

theorem splitEvaluation_first (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    splitEvaluation p (AddMonoidAlgebra.single (1, 0) 1) = (parameterEquiv p : E) := rfl

theorem splitEvaluation_second (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    splitEvaluation p (AddMonoidAlgebra.single (0, 1) 1) = conjugation (parameterEquiv p : E) := by
  have h := splitEvaluation_conjugation p (AddMonoidAlgebra.single (1, 0) 1)
  simpa only [SplitLaurentGalois.conjugate_single, map_one, Prod.swap_prod_mk,
    splitEvaluation_first] using h

private theorem split_coordinates (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    SplitLaurentPoints.coordinates (splitEvaluation p) =
      (parameterEquiv p, Units.map conjugation.toMonoidHom (parameterEquiv p)) := by
  apply Prod.ext <;> apply Units.ext
  · exact splitEvaluation_first p
  · exact splitEvaluation_second p

theorem splitEvaluation_monomial (p : quotientFixedRing →ₐ[ℚ] ℚ) (n : ℤ × ℤ) :
    splitEvaluation p (AddMonoidAlgebra.single n 1) =
      (parameterEquiv p : E) ^ n.1 * conjugation (parameterEquiv p : E) ^ n.2 := by
  conv_lhs => rw [← evaluate_coordinates (splitEvaluation p), split_coordinates]
  simp [evaluate_single]

theorem linearExpression_image :
    fixedRingEquiv ⟨linearExpression, linearExpression_fixed⟩ = linearCoefficient :=
  Subtype.ext linearExpression_pullback

theorem constantExpression_image :
    fixedRingEquiv ⟨constantExpression, constantExpression_fixed⟩ = constantCoefficient :=
  Subtype.ext constantExpression_pullback

/-- The descended linear coefficient is the norm expression. -/
theorem linearCoefficient_eq (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    p linearCoefficient = (1 - Algebra.norm ℚ (parameterEquiv p : E)) / 3 := by
  apply (algebraMap ℚ E).injective
  have h := splitEvaluation_fixed p ⟨linearExpression, linearExpression_fixed⟩
  rw [linearExpression_image] at h
  rw [← h]
  change splitEvaluation p linearExpression = _
  unfold linearExpression
  rw [map_rat_smul]
  simp only [map_sub, map_one, splitEvaluation_monomial,
    zpow_one, Algebra.smul_def, map_div₀, map_ofNat, norm_eq_mul_conjugation]
  ring

/-- The constant coefficient formula also holds on points with no rational cover lift. -/
theorem constantCoefficient_eq (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    p constantCoefficient =
      (Algebra.norm ℚ (parameterEquiv p : E) *
        (3 - Algebra.trace ℚ E (parameterEquiv p : E)) - 1) / 27 := by
  apply (algebraMap ℚ E).injective
  have h := splitEvaluation_fixed p ⟨constantExpression, constantExpression_fixed⟩
  rw [constantExpression_image] at h
  rw [← h]
  change splitEvaluation p constantExpression = _
  unfold constantExpression
  rw [map_rat_smul]
  simp only [map_sub, map_mul, map_one, map_ofNat,
    splitEvaluation_monomial, zpow_ofNat, Algebra.smul_def, map_div₀,
    norm_eq_mul_conjugation, trace_eq_add_conjugation]
  ring

/-- The paper's cubic formula for every rational point of the descended quotient. -/
theorem characteristicPolynomial_eq (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    characteristicPolynomial p =
      CorrespondencePolynomials.cubic ((1 - Algebra.norm ℚ (parameterEquiv p : E)) / 3)
        ((Algebra.norm ℚ (parameterEquiv p : E) *
          (3 - Algebra.trace ℚ E (parameterEquiv p : E)) - 1) / 27) := by
  rw [characteristicPolynomial, linearCoefficient_eq, constantCoefficient_eq]

theorem inverse_denominator_ne_zero (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    1 - 3 * p linearCoefficient ≠ 0 := by
  rw [linearCoefficient_eq]
  have h := norm_pos (parameterEquiv p).ne_zero
  have he : 1 - 3 * ((1 - Algebra.norm ℚ (parameterEquiv p : E)) / 3) =
      Algebra.norm ℚ (parameterEquiv p : E) := by ring
  rw [he]
  exact ne_of_gt h

end Cubic.QuadraticCorrespondence.RationalCoefficientFormula
