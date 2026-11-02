import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Cubic.QuadraticCorrespondence.CyclotomicCoefficients
import Mathlib.Tactic.NormNum

/-!
# Coefficients and integrality of the correspondence polynomials

These lemmas concern the exact displayed polynomials. Their application to
the original quotient points uses the separately proved descended coefficient
formulas in `RationalCoefficientFormula`.
-/

namespace Cubic.QuadraticCorrespondence.CorrespondencePolynomials

open Polynomial CyclotomicCoefficients

@[simp]
theorem cubic_coeff_zero (a b : ℚ) : (cubic a b).coeff 0 = b := by simp [cubic]

@[simp]
theorem cubic_coeff_one (a b : ℚ) : (cubic a b).coeff 1 = a := by simp [cubic]

@[simp]
theorem cubic_coeff_two (a b : ℚ) : (cubic a b).coeff 2 = -1 := by simp [cubic]

@[simp]
theorem cubic_coeff_three (a b : ℚ) : (cubic a b).coeff 3 = 1 := by simp [cubic]

theorem cubic_eq_iff {a b c d : ℚ} : cubic a b = cubic c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : ℚ[X] => f.coeff 1) h,
      by simpa using congrArg (fun f : ℚ[X] => f.coeff 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem cubic_integral_iff (a b : ℚ) :
    HasIntegralCoefficients (cubic a b) ↔
      (∃ m : ℤ, a = (m : ℚ)) ∧ (∃ n : ℤ, b = (n : ℚ)) := by
  constructor
  · intro h
    exact ⟨by simpa using h 1, by simpa using h 0⟩
  · rintro ⟨ha, hb⟩ n
    by_cases h0 : n = 0
    · simpa [h0] using hb
    by_cases h1 : n = 1
    · simpa [h1] using ha
    by_cases h2 : n = 2
    · exact ⟨-1, by simp [h2]⟩
    by_cases h3 : n = 3
    · exact ⟨1, by simp [h3]⟩
    exact ⟨0, by simp [cubic, coeff_X, coeff_C, h0, Ne.symm h1, h2, h3]⟩

theorem linear_integral_iff (N : ℚ) :
    (∃ m : ℤ, (1 - N) / 3 = (m : ℚ)) ↔
      ∃ m : ℤ, N = 1 + 3 * (m : ℚ) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast
    linarith

theorem constant_integral_iff (N T : ℚ) :
    (∃ n : ℤ, (N * (3 - T) - 1) / 27 = (n : ℚ)) ↔
      ∃ n : ℤ, N * (3 - T) = 1 + 27 * (n : ℚ) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩

/-- The exact two integer congruences in `eqn:integralityConditionsUsingCyclo`. -/
theorem cyclotomic_integral_iff (u v : ℚ) :
    HasIntegralCoefficients (cubic (linearCoefficient u v) (constantCoefficient u v)) ↔
      (∃ m : ℤ, normForm u v = 1 + 3 * (m : ℚ)) ∧
      (∃ n : ℤ, normForm u v * (3 - traceForm u v) = 1 + 27 * (n : ℚ)) := by
  rw [cubic_integral_iff, linearCoefficient, constantCoefficient,
    linear_integral_iff, constant_integral_iff]

end Cubic.QuadraticCorrespondence.CorrespondencePolynomials
