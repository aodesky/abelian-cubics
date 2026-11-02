import Cubic.QuadraticCorrespondence.QuotientNormCharacter
import Cubic.ToricHeights.QuotientFiniteHeight
import Cubic.ToricHeights.QuotientLocalIntegrality
import Cubic.ToricHeights.ArchimedeanQuotientLogarithm

/-!
# Local logarithms paired with the original rational norm character

The norm character is descended from the product of the two quotient
characters. Compare its values with the split product and
the inert, ramified and archimedean squared norms. The original weighted
logarithms then have coordinates `(-log |N(P)|/2, -log |N(P)|/2)`.
These are local identities; triviality on rational points follows with the
product formula (`Cubic.PoissonSummation.AdelicRationalCharacter`).
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientNormLogarithm

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois QuotientNormCharacter
open QuotientFiniteHeight LocalLogarithmNormalization
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

theorem split_value [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    (value ℚ_[p] P : ℚ_[p]) =
      ((SplitQuotientLogarithm.localPoint p P).1 : ℚ_[p]) *
        ((SplitQuotientLogarithm.localPoint p P).2 : ℚ_[p]) := by
  rw [value_eq_coefficient, (QuotientLocalIntegrality.split_coefficients p P).1]
  ring

theorem split_logarithm [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitLogarithm p P =
      (-Real.log ‖(value ℚ_[p] P : ℚ_[p])‖ / 2,
       -Real.log ‖(value ℚ_[p] P : ℚ_[p])‖ / 2) := by
  rw [splitLogarithm_eq, split_averaged_log_norm, split_value, norm_mul]

theorem inert_norm_value [Fact (p % 3 = 2)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ‖(value ℚ_[p] P : ℚ_[p])‖ =
      ‖(InertQuotientLogarithm.localPoint p P : CyclotomicInertField.Extension p)‖ ^ 2 := by
  obtain ⟨a, b, hx⟩ := CyclotomicInertField.exists_linear p
    (InertQuotientLogarithm.localPoint p P : CyclotomicInertField.Extension p)
  have hv : (value ℚ_[p] P : ℚ_[p]) = CyclotomicCoefficients.normForm a b := by
    rw [value_eq_coefficient, (QuotientLocalIntegrality.inert_coefficients p P a b hx).1]
    unfold CyclotomicCoefficients.linearCoefficient
    ring
  rw [hv, hx, InertLocalIntegrality.norm_normForm]

theorem inert_logarithm [Fact (p % 3 = 2)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertLogarithm p P =
      (-Real.log ‖(value ℚ_[p] P : ℚ_[p])‖ / 2,
       -Real.log ‖(value ℚ_[p] P : ℚ_[p])‖ / 2) := by
  have h := inert_log_norm p (InertQuotientLogarithm.localPoint p P)
  rw [InertLocalModel.degree_eq_two_ord] at h
  push_cast at h
  rw [inertLogarithm_eq, inert_rayCoordinates, inert_norm_value, Real.log_pow]
  ext <;> simp only [normalizedLog] <;> nlinarith

theorem ramified_norm_value (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ‖(value ℚ_[3] P : ℚ_[3])‖ =
      ‖(RamifiedQuotientLogarithm.localPoint P : CyclotomicRamifiedField.Extension)‖ ^ 2 := by
  obtain ⟨a, b, hx⟩ := CyclotomicRamifiedField.exists_linear
    (RamifiedQuotientLogarithm.localPoint P : CyclotomicRamifiedField.Extension)
  have hv : (value ℚ_[3] P : ℚ_[3]) = CyclotomicCoefficients.normForm a b := by
    rw [value_eq_coefficient, (QuotientLocalIntegrality.ramified_coefficients P a b hx).1]
    unfold CyclotomicCoefficients.linearCoefficient
    ring
  rw [hv, hx, RamifiedLocalIntegrality.norm_normForm]

theorem ramified_logarithm (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedLogarithm P =
      (-Real.log ‖(value ℚ_[3] P : ℚ_[3])‖ / 2,
       -Real.log ‖(value ℚ_[3] P : ℚ_[3])‖ / 2) := by
  have h := ramified_log_norm (RamifiedQuotientLogarithm.localPoint P)
  rw [ramifiedLogarithm_eq, ramified_norm_value, Real.log_pow]
  ext <;> simp only [normalizedLog, RamifiedLocalModel.rayCoordinates] <;>
    dsimp [RamifiedLocalModel.degree] at h ⊢ <;> nlinarith

theorem infinite_value (P : ArchimedeanQuotientLogarithm.Points) :
    (value ℝ P : ℝ) = ‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖ ^ 2 := by
  have h := congrArg CyclotomicArchimedean.place (value_tensor ℝ P)
  rw [CyclotomicArchimedean.place_scalar] at h
  have he : (↑(value ℝ P) : ℂ) =
      (QuotientLocalCharacters.localCharacter ℝ CyclotomicArchimedean.place.toRingHom P
        (Multiplicative.ofAdd (1, 1)) : ℂ) := h
  rw [ArchimedeanQuotientLogarithm.normCharacterValue_eq] at he
  exact Complex.ofReal_injective he

theorem infinite_value_pos (P : ArchimedeanQuotientLogarithm.Points) : 0 < (value ℝ P : ℝ) := by
  rw [infinite_value]
  exact sq_pos_of_pos (norm_pos_iff.mpr (CyclotomicArchimedean.pointEquiv P).ne_zero)

theorem infinite_logarithm (P : ArchimedeanQuotientLogarithm.Points) :
    ArchimedeanQuotientLogarithm.logarithm P =
      (-Real.log ‖(value ℝ P : ℝ)‖ / 2, -Real.log ‖(value ℝ P : ℝ)‖ / 2) := by
  rw [ArchimedeanQuotientLogarithm.logarithm_eq, Real.norm_of_nonneg (infinite_value_pos P).le,
    infinite_value, Real.log_pow]
  ext <;> dsimp [ArchimedeanQuotientLogarithm.coordinate] <;> ring

end Cubic.ToricHeights.QuotientNormLogarithm
