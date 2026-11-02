import Cubic.QuadraticCorrespondence.DescendedCoefficients
import Cubic.QuadraticCorrespondence.QuotientLocalCharacters

/-!
# Descended coefficient formulas after a local place map

Evaluate the original symmetric coefficient functions on an arbitrary point of
the descended quotient over a rational algebra. After any place map to a
characteristic-zero field, they have the stated norm/trace expressions in the
two quotient characters. The coefficients are defined from the universal
augmentation-one cover; the point need not lift to the cover.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientCoefficientFormula

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicPointDescent
open CyclotomicRestrictionScalars RationalQuotientGroup QuotientLocalCharacters
open SplitLaurentInvariants SplitLaurentPoints SplitLaurentEvaluation DescendedCoefficients

variable (A : Type*) [CommRing A] [Algebra ℚ A]
variable {L : Type*} [Field L]
variable (place : E ⊗[ℚ] A →+* L)

/-- Scalar extension and local evaluation in the quotient Laurent presentation. -/
def evaluation (P : quotientFixedRing →ₐ[ℚ] A) : CoverRing →+* L :=
  place.comp (extendPoint (quotientPresentation A P)).toRingHom

theorem evaluation_fixed (P : quotientFixedRing →ₐ[ℚ] A) (b : coverFixedRing) :
    evaluation A place P (b : CoverRing) = place ((1 : E) ⊗ₜ[ℚ] P (fixedRingEquiv b)) := by
  change place (extendPoint (quotientPresentation A P) (b : CoverRing)) = _
  rw [extendPoint_fixed]
  rfl

/-- Every Laurent monomial evaluates in the two quotient characters. -/
theorem evaluation_monomial (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    evaluation A place P (AddMonoidAlgebra.single m 1) =
      place (quotientRestrictionScalarsEquiv A P : E ⊗[ℚ] A) ^ m.1 *
        place (conjugateUnit A (quotientRestrictionScalarsEquiv A P) : E ⊗[ℚ] A) ^ m.2 := by
  have h := (pointCharacter_coordinates (extendPoint (quotientPresentation A P)) m).symm
  rw [extended_coordinates] at h
  have he := congrArg (fun u : (E ⊗[ℚ] A)ˣ => (Units.map place.toMonoidHom u : L)) h
  simpa [pointCharacter, evaluation] using he

variable [CharZero L]

/-- The original linear coefficient is `(1-N)/3` at every local quotient point. -/
theorem linearCoefficient_eq (P : quotientFixedRing →ₐ[ℚ] A) :
    place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient) =
      (1 - place (quotientRestrictionScalarsEquiv A P : E ⊗[ℚ] A) *
        place (conjugateUnit A (quotientRestrictionScalarsEquiv A P) : E ⊗[ℚ] A)) / 3 := by
  have himage : fixedRingEquiv ⟨linearExpression, linearExpression_fixed⟩ = linearCoefficient :=
    Subtype.ext linearExpression_pullback
  have h := evaluation_fixed A place P ⟨linearExpression, linearExpression_fixed⟩
  rw [himage] at h
  rw [← h]
  change evaluation A place P linearExpression = _
  simp only [linearExpression, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap,
    map_sub, map_one, evaluation_monomial, zpow_one, map_div₀, map_ofNat]
  ring

/-- The original constant coefficient has the sign `(N(3-T)-1)/27`. -/
theorem constantCoefficient_eq (P : quotientFixedRing →ₐ[ℚ] A) :
    place ((1 : E) ⊗ₜ[ℚ] P constantCoefficient) =
      (place (quotientRestrictionScalarsEquiv A P : E ⊗[ℚ] A) *
          place (conjugateUnit A (quotientRestrictionScalarsEquiv A P) : E ⊗[ℚ] A) *
        (3 - (place (quotientRestrictionScalarsEquiv A P : E ⊗[ℚ] A) +
          place (conjugateUnit A (quotientRestrictionScalarsEquiv A P) : E ⊗[ℚ] A))) - 1) / 27 := by
  have himage : fixedRingEquiv ⟨constantExpression, constantExpression_fixed⟩ = constantCoefficient :=
    Subtype.ext constantExpression_pullback
  have h := evaluation_fixed A place P ⟨constantExpression, constantExpression_fixed⟩
  rw [himage] at h
  rw [← h]
  change evaluation A place P constantExpression = _
  simp only [constantExpression, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap,
    map_sub, map_one, map_ofNat, evaluation_monomial, zpow_ofNat, map_div₀]
  ring

/-- Descend both formulas to the coefficient field once the local
product and sum of conjugate characters are identified with `N` and `T`. -/
theorem coefficients_eq_of_norm_trace {K : Type*} [Field K] [CharZero K]
    (base : K →+* L) (localPlace : E ⊗[ℚ] K →+* L)
    (hbase : ∀ a : K, localPlace ((1 : E) ⊗ₜ[ℚ] a) = base a)
    (P : quotientFixedRing →ₐ[ℚ] K) (N T : K)
    (hN : localPlace (quotientRestrictionScalarsEquiv K P : E ⊗[ℚ] K) *
      localPlace (conjugateUnit K (quotientRestrictionScalarsEquiv K P) : E ⊗[ℚ] K) = base N)
    (hT : localPlace (quotientRestrictionScalarsEquiv K P : E ⊗[ℚ] K) +
      localPlace (conjugateUnit K (quotientRestrictionScalarsEquiv K P) : E ⊗[ℚ] K) = base T) :
    P linearCoefficient = (1 - N) / 3 ∧
      P constantCoefficient = (N * (3 - T) - 1) / 27 := by
  constructor
  · apply base.injective
    rw [← hbase (P linearCoefficient), linearCoefficient_eq, hN]
    simp only [map_div₀, map_sub, map_one, map_ofNat]
  · apply base.injective
    rw [← hbase (P constantCoefficient), constantCoefficient_eq, hN, hT]
    simp only [map_div₀, map_sub, map_mul, map_one, map_ofNat]

end Cubic.QuadraticCorrespondence.QuotientCoefficientFormula
