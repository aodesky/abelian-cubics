import Cubic.QuadraticCorrespondence.RationalCoefficientFormula
import Cubic.QuadraticCorrespondence.CorrespondencePolynomialArithmetic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The inverse quadratic and integrality on the rational quotient

These are assertions about the descended cubic on every rational quotient
point. The Galois classification, the fibre counts and the canonical toric-height
comparison are proved in `QuotientCubicClassification`,
`QuotientPolynomialConverse` and `CyclotomicParametrizationAssembly`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalCorrespondence

open Polynomial CyclotomicField CyclotomicTorusGalois DescendedCoefficients
open RationalCoefficientFormula CorrespondencePolynomials

theorem recovered_norm (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    1 - 3 * p linearCoefficient = Algebra.norm ℚ (parameterEquiv p : E) := by
  rw [linearCoefficient_eq]
  ring

theorem recovered_trace (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    3 - (1 + 27 * p constantCoefficient) / (1 - 3 * p linearCoefficient) =
      Algebra.trace ℚ E (parameterEquiv p : E) := by
  rw [recovered_norm, constantCoefficient_eq]
  have hn : Algebra.norm ℚ (parameterEquiv p : E) ≠ 0 :=
    ne_of_gt (norm_pos (parameterEquiv p).ne_zero)
  field_simp
  ring

/-- The inverse quadratic is the norm/trace polynomial of the parameter. -/
theorem inverseQuadratic_eq (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    inverseQuadratic (p linearCoefficient) (p constantCoefficient) =
      X ^ 2 - C (Algebra.trace ℚ E (parameterEquiv p : E)) * X +
        C (Algebra.norm ℚ (parameterEquiv p : E)) := by
  rw [inverseQuadratic, recovered_trace, recovered_norm]

theorem inverseQuadratic_root (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    Polynomial.eval (parameterEquiv p : E)
      ((inverseQuadratic (p linearCoefficient) (p constantCoefficient)).map (algebraMap ℚ E)) = 0 := by
  rw [inverseQuadratic_eq]
  simpa using quadratic_norm_trace (parameterEquiv p : E)

/-- The inverse-quadratic clause with arbitrary coefficients of the associated cubic. -/
theorem inverse_quadratic (a b : ℚ) (p : quotientFixedRing →ₐ[ℚ] ℚ)
    (h : characteristicPolynomial p = cubic a b) :
    Polynomial.eval (parameterEquiv p : E) ((inverseQuadratic a b).map (algebraMap ℚ E)) = 0 := by
  obtain ⟨ha, hb⟩ := cubic_eq_iff.mp h
  rw [← ha, ← hb]
  exact inverseQuadratic_root p

/-- The proposition's integrality criterion for the descended original coefficients. -/
theorem integrality_iff (p : quotientFixedRing →ₐ[ℚ] ℚ) (u v : ℚ)
    (h : (parameterEquiv p : E) = algebraMap ℚ E u + algebraMap ℚ E v * zeta) :
    HasIntegralCoefficients (characteristicPolynomial p) ↔
      (∃ m : ℤ, CyclotomicCoefficients.normForm u v = 1 + 3 * (m : ℚ)) ∧
      (∃ n : ℤ, CyclotomicCoefficients.normForm u v *
        (3 - CyclotomicCoefficients.traceForm u v) = 1 + 27 * (n : ℚ)) := by
  rw [characteristicPolynomial_eq, h, norm_linear, trace_linear]
  exact cyclotomic_integral_iff u v

/-- The coefficient expression for the height agrees with the norm.
Its identification with the canonical toric height is in
`CyclotomicParametrizationAssembly`. -/
theorem sqrt_coefficient_eq_sqrt_norm (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    Real.sqrt (1 - 3 * (p linearCoefficient : ℝ)) =
      Real.sqrt (Algebra.norm ℚ (parameterEquiv p : E) : ℝ) := by
  congr 1
  exact_mod_cast recovered_norm p

end Cubic.QuadraticCorrespondence.RationalCorrespondence
