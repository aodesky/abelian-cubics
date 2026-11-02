import Cubic.QuadraticCorrespondence.QuotientLocalCharacters
import Cubic.QuadraticCorrespondence.DescendedCoefficients

/-!
# The original rational norm character

Descend the product of the two quotient characters as a unit of the rational
invariant ring. Its evaluation is multiplicative and natural in coefficient
algebras. The product-of-conjugates and original coefficient formulas are
proved from this definition.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientNormCharacter

open CyclotomicField CyclotomicTorusGalois CyclotomicPointDescent
open CyclotomicRestrictionScalars RationalQuotientGroup QuotientLocalCharacters
open DescendedCoefficients
open scoped TensorProduct RationalQuotientGroup

/-- Diagonal Laurent monomials are fixed by the original Galois involution. -/
def diagonalMonomial (k : ℤ) : coverFixedRing :=
  ⟨AddMonoidAlgebra.single (k, k) 1, by
    change SplitLaurentGalois.conjugate conjugation _ = _
    simp only [SplitLaurentGalois.conjugate_single, map_one, Prod.swap_prod_mk,
      AlgHom.id_apply]⟩

private def diagonalUnit : coverFixedRingˣ where
  val := diagonalMonomial 1
  inv := diagonalMonomial (-1)
  val_inv := by
    apply Subtype.ext
    simp [diagonalMonomial, AddMonoidAlgebra.single_mul_single]
    rfl
  inv_val := by
    apply Subtype.ext
    simp [diagonalMonomial, AddMonoidAlgebra.single_mul_single]
    rfl

/-- The product character `(1,1)`, descended to the original rational quotient ring. -/
def normCharacter : quotientFixedRingˣ := Units.map fixedRingEquiv.toMonoidHom diagonalUnit

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Evaluation of the norm character on an original point. -/
def value (P : quotientFixedRing →ₐ[ℚ] A) : Aˣ := Units.map P.toMonoidHom normCharacter

/-- Scalar extension recovers the original quotient character `(1,1)`. -/
theorem value_tensor (P : quotientFixedRing →ₐ[ℚ] A) :
    (1 : E) ⊗ₜ[ℚ] (value A P : A) =
      (characterValues A P (Multiplicative.ofAdd (1, 1)) : E ⊗[ℚ] A) := by
  rw [characterValues_eq]
  exact (extendPoint_fixed (quotientPresentation A P) (diagonalMonomial 1)).symm

theorem value_mul (P Q : quotientFixedRing →ₐ[ℚ] A) :
    value A (P * Q) = value A P * value A Q := by
  apply Units.ext
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] (value A (P * Q) : A) =
    (1 : E) ⊗ₜ[ℚ] ((value A P : A) * (value A Q : A))
  rw [value_tensor, characterValues_mul]
  rw [← one_mul (1 : E), ← Algebra.TensorProduct.tmul_mul_tmul, value_tensor, value_tensor]
  rfl

/-- The norm character is natural under every rational coefficient-algebra map. -/
theorem value_comp {B : Type*} [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (P : quotientFixedRing →ₐ[ℚ] A) :
    value B (φ.comp P) = Units.map φ.toMonoidHom (value A P) := rfl

/-- Under the specified quotient parametrization it is the product of conjugates. -/
theorem value_tensor_eq_product (P : quotientFixedRing →ₐ[ℚ] A) :
    (1 : E) ⊗ₜ[ℚ] (value A P : A) =
      (quotientRestrictionScalarsEquiv A P : E ⊗[ℚ] A) *
        (conjugateUnit A (quotientRestrictionScalarsEquiv A P) : E ⊗[ℚ] A) := by
  rw [value_tensor, characterValues_formula]
  simp

/-- The relation to the original elementary symmetric coefficient is a theorem. -/
theorem normCharacter_coefficient :
    (normCharacter : quotientFixedRing) = 1 - 3 * linearCoefficient := by
  have he : fixedRingEquiv ⟨linearExpression, linearExpression_fixed⟩ = linearCoefficient :=
    Subtype.ext linearExpression_pullback
  calc
    _ = fixedRingEquiv (1 - 3 * ⟨linearExpression, linearExpression_fixed⟩) := by
      change fixedRingEquiv (diagonalMonomial 1) = _
      congr 1
      apply Subtype.ext
      change AddMonoidAlgebra.single (1, 1) (1 : E) = 1 - 3 * linearExpression
      have hs : (3 : CoverRing) * linearExpression =
          1 - AddMonoidAlgebra.single (1, 1) (1 : E) := by
        calc
          _ = (3 : ℚ) • linearExpression := by simp only [Algebra.smul_def, map_ofNat]
          _ = _ := by rw [linearExpression, smul_smul]; norm_num
      rw [hs]
      ring
    _ = _ := by simp only [map_sub, map_mul, map_one, map_ofNat, he]

theorem value_eq_coefficient (P : quotientFixedRing →ₐ[ℚ] A) :
    (value A P : A) = 1 - 3 * P linearCoefficient := by
  change P (normCharacter : quotientFixedRing) = _
  rw [normCharacter_coefficient]
  simp only [map_sub, map_mul, map_one, map_ofNat]

end Cubic.QuadraticCorrespondence.QuotientNormCharacter
