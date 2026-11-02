import Cubic.QuadraticCorrespondence.RationalQuotientFunctor
import Cubic.QuadraticCorrespondence.SplitQuotientGroup

/-!
# Descent of the original quotient group law

Galois-equivariant Laurent points form a subgroup for the coordinate-ring
coproduct law. Effective descent supplies the group on rational fixed-ring
points. On the cyclic quotient, scalar extension recovers the invariant-ring
coproduct law checked in `SplitQuotientGroup`. The original cover restricts
multiplicatively, and the specified restriction-of-scalars comparison is a
natural group isomorphism on all commutative rational coefficient algebras.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalQuotientGroup

open scoped TensorProduct LaurentPointGroup
open CyclotomicField CyclotomicTorusGalois CyclotomicPointDescent CyclotomicRestrictionScalars
open SplitLaurentInvariants SplitLaurentPoints SplitLaurentGalois SplitCoverFunctor
open RationalCoverFunctor RationalQuotientFunctor
open Cubic.OrbitParametrization.CyclicGroupAlgebra

variable (A : Type*) [CommRing A] [Algebra ℚ A]

private theorem equivariant_iff (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A) :
    IsEquivariant f ↔
      pointConjugate (baseChangeConjugation A) (LaurentPointGroup.coordinatesMulEquiv f) =
        LaurentPointGroup.coordinatesMulEquiv f := by
  simpa only [evaluate_coordinates] using evaluate_equivariant_iff A (coordinates f)

/-- The subgroup is defined by Galois compatibility, before parametrizing it. -/
def equivariantSubgroup : Subgroup (LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A) where
  carrier := {f | IsEquivariant f}
  one_mem' := by
    change IsEquivariant _
    rw [equivariant_iff, map_one]
    simp [pointConjugate]
  mul_mem' := by
    intro f g hf hg
    change IsEquivariant f at hf
    change IsEquivariant g at hg
    change IsEquivariant _
    rw [equivariant_iff] at hf hg ⊢
    rw [map_mul]
    have hm (x y : (E ⊗[ℚ] A)ˣ × (E ⊗[ℚ] A)ˣ) :
        pointConjugate (baseChangeConjugation A) (x * y) =
          pointConjugate (baseChangeConjugation A) x * pointConjugate (baseChangeConjugation A) y := by
      ext <;> simp [pointConjugate]
    rw [hm, hf, hg]
  inv_mem' := by
    intro f hf
    change IsEquivariant f at hf
    change IsEquivariant _
    rw [equivariant_iff] at hf ⊢
    rw [map_inv]
    have hi (x : (E ⊗[ℚ] A)ˣ × (E ⊗[ℚ] A)ˣ) :
        pointConjugate (baseChangeConjugation A) x⁻¹ =
          (pointConjugate (baseChangeConjugation A) x)⁻¹ := by
      ext <;> simp [pointConjugate]
    rw [hi, hf]

/-- The descended group law is obtained from equivariant coordinate-ring points. -/
scoped instance coverPointGroup : CommGroup (coverFixedRing →ₐ[ℚ] A) :=
  (show (coverFixedRing →ₐ[ℚ] A) ≃ equivariantSubgroup A from equivariantPointEquiv).commGroup

def extendMulEquiv : (coverFixedRing →ₐ[ℚ] A) ≃* equivariantSubgroup A :=
  { equivariantPointEquiv with map_mul' := fun _ _ => equivariantPointEquiv.apply_symm_apply _ }

theorem extendPoint_mul (f g : coverFixedRing →ₐ[ℚ] A) :
    extendPoint (f * g) = extendPoint f * extendPoint g :=
  congrArg Subtype.val ((extendMulEquiv A).map_mul f g)

/-- Pullback by the invariant-ring presentation, before using any field-unit comparison. -/
def quotientPresentation : (quotientFixedRing →ₐ[ℚ] A) ≃ (coverFixedRing →ₐ[ℚ] A) :=
  fixedRingEquiv.symm.arrowCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)

scoped instance quotientPointGroup : CommGroup (quotientFixedRing →ₐ[ℚ] A) :=
  (quotientPresentation A).commGroup

def quotientPresentationMulEquiv :
    (quotientFixedRing →ₐ[ℚ] A) ≃* (coverFixedRing →ₐ[ℚ] A) :=
  { quotientPresentation A with map_mul' := fun _ _ => (quotientPresentation A).apply_symm_apply _ }

/-- Scalar extension as a point of the split invariant ring. -/
def extendQuotient (p : quotientFixedRing →ₐ[ℚ] A) :
    invariantRing (rootUnit zeta zeta_relation) →ₐ[E] E ⊗[ℚ] A :=
  (extendPoint (quotientPresentation A p)).comp
    (invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)).symm.toAlgHom

/-- This extension agrees with the natural map on the original fixed functions. -/
theorem extendQuotient_fixed (p : quotientFixedRing →ₐ[ℚ] A) (b : quotientFixedRing) :
    extendQuotient A p ⟨b, b.property.2⟩ = (1 : E) ⊗ₜ[ℚ] p b := by
  obtain ⟨c, rfl⟩ := fixedRingEquiv.surjective b
  change extendPoint (quotientPresentation A p)
    ((invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)).symm
      ((invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)) c)) = _
  rw [AlgEquiv.symm_apply_apply, extendPoint_fixed]
  rfl

theorem presentation_extendQuotient (p : quotientFixedRing →ₐ[ℚ] A) :
    SplitQuotientGroup.presentation (rootUnit zeta zeta_relation)
      (rootUnit_primitive zeta zeta_relation) (extendQuotient A p) =
        extendPoint (quotientPresentation A p) := by
  apply AlgHom.ext
  intro b
  change extendPoint (quotientPresentation A p)
    ((invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)).symm
      ((invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)) b)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- The descended law extends to the restriction of the original cover coproduct.
This identifies the quotient group law without using the cyclotomic isomorphism. -/
theorem extendQuotient_mul (p q : quotientFixedRing →ₐ[ℚ] A) :
    letI := SplitQuotientGroup.pointGroup (rootUnit zeta zeta_relation)
      (rootUnit_primitive zeta zeta_relation) (R := E ⊗[ℚ] A)
    extendQuotient A (p * q) = extendQuotient A p * extendQuotient A q := by
  letI := SplitQuotientGroup.pointGroup (rootUnit zeta zeta_relation)
    (rootUnit_primitive zeta zeta_relation) (R := E ⊗[ℚ] A)
  apply (SplitQuotientGroup.presentationMulEquiv (rootUnit zeta zeta_relation)
    (rootUnit_primitive zeta zeta_relation)).injective
  rw [map_mul]
  change SplitQuotientGroup.presentation _ _ (extendQuotient A (p * q)) =
    SplitQuotientGroup.presentation _ _ (extendQuotient A p) *
      SplitQuotientGroup.presentation _ _ (extendQuotient A q)
  rw [presentation_extendQuotient, presentation_extendQuotient, presentation_extendQuotient]
  change extendPoint (quotientPresentationMulEquiv A (p * q)) =
    extendPoint (quotientPresentationMulEquiv A p) * extendPoint (quotientPresentationMulEquiv A q)
  rw [map_mul, extendPoint_mul]

/-- The natural point bijection `restrictionScalarsEquiv` preserves the descended group law. -/
def restrictionScalarsMulEquiv : (coverFixedRing →ₐ[ℚ] A) ≃* (E ⊗[ℚ] A)ˣ :=
  { restrictionScalarsEquiv A with
    map_mul' := by
      intro f g
      change (coordinates (extendPoint (f * g))).1 =
        (coordinates (extendPoint f)).1 * (coordinates (extendPoint g)).1
      rw [extendPoint_mul, LaurentPointGroup.coordinates_mul]
      rfl }

/-- The specified quotient-character parametrization as a group isomorphism. -/
def quotientRestrictionScalarsMulEquiv : (quotientFixedRing →ₐ[ℚ] A) ≃* (E ⊗[ℚ] A)ˣ :=
  (quotientPresentationMulEquiv A).trans (restrictionScalarsMulEquiv A)

theorem quotientRestrictionScalarsMulEquiv_apply (p : quotientFixedRing →ₐ[ℚ] A) :
    quotientRestrictionScalarsMulEquiv A p = quotientRestrictionScalarsEquiv A p := rfl

theorem quotientRestrictionScalarsMulEquiv_comp {B : Type*} [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (p : quotientFixedRing →ₐ[ℚ] A) :
    quotientRestrictionScalarsMulEquiv B (φ.comp p) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom
        (quotientRestrictionScalarsMulEquiv A p) :=
  quotientRestrictionScalarsEquiv_comp A φ p

/-- The original rational cover-to-quotient map is a group homomorphism. -/
theorem quotientPoint_mul (g h : traceOneUnits A) :
    quotientPoint A (g * h) = quotientPoint A g * quotientPoint A h := by
  apply (quotientRestrictionScalarsMulEquiv A).injective
  rw [map_mul]
  change quotientRestrictionScalarsEquiv A (quotientPoint A (g * h)) =
    quotientRestrictionScalarsEquiv A (quotientPoint A g) *
      quotientRestrictionScalarsEquiv A (quotientPoint A h)
  rw [quotientPoint_unit_formula, quotientPoint_unit_formula, quotientPoint_unit_formula, map_mul]
  simp only [conjugateUnit, map_mul]
  rw [mul_pow (coverUnitEquiv A g) (coverUnitEquiv A h)]
  exact mul_div_mul_comm (a := coverUnitEquiv A g ^ 2) (b := coverUnitEquiv A h ^ 2)
    (c := conjugateUnit A (coverUnitEquiv A g)) (d := conjugateUnit A (coverUnitEquiv A h))

/-- Naturality includes the group law on quotient points. -/
def mapPoint {B : Type*} [CommRing B] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    (quotientFixedRing →ₐ[ℚ] A) →* (quotientFixedRing →ₐ[ℚ] B) where
  toFun p := φ.comp p
  map_one' := by
    apply (quotientRestrictionScalarsMulEquiv B).injective
    rw [quotientRestrictionScalarsMulEquiv_comp, map_one, map_one, map_one]
  map_mul' p q := by
    apply (quotientRestrictionScalarsMulEquiv B).injective
    simp only [quotientRestrictionScalarsMulEquiv_comp, map_mul]

end Cubic.QuadraticCorrespondence.RationalQuotientGroup
