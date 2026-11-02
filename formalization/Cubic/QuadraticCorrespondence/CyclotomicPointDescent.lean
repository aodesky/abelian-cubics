import Cubic.QuadraticCorrespondence.CyclotomicScalarDescent

/-!
# Descent of points of the Laurent coordinate ring

A point of the rational fixed ring extends to an equivariant point of the
split Laurent ring over `E ⊗[ℚ] A`. Conversely every such equivariant point
descends uniquely. These maps use the natural base-change isomorphism and
the proved coefficient descent, and work for every commutative rational algebra.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicPointDescent

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicTorusDescent SplitLaurentInvariants

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Extend a rational point using the natural scalar-extension isomorphism. -/
def extendPoint (f : coverFixedRing →ₐ[ℚ] A) :
    LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A :=
  (Algebra.TensorProduct.map (AlgHom.id E E) f).comp coverBaseChangeEquiv.symm.toAlgHom

@[simp]
theorem extendPoint_fixed (f : coverFixedRing →ₐ[ℚ] A) (b : coverFixedRing) :
    extendPoint f (b : LaurentRing (K := E)) = (1 : E) ⊗ₜ[ℚ] f b := by
  have hb : coverBaseChangeEquiv.symm (b : LaurentRing (K := E)) = (1 : E) ⊗ₜ[ℚ] b := by
    apply coverBaseChangeEquiv.injective
    simp
  simp [extendPoint, hb]

theorem extendPoint_conjugate (f : coverFixedRing →ₐ[ℚ] A) (b : LaurentRing (K := E)) :
    extendPoint f (SplitLaurentGalois.conjugate conjugation b) =
      baseChangeConjugation A (extendPoint f b) := by
  obtain ⟨x, rfl⟩ := coverBaseChangeEquiv.surjective b
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    rw [coverBaseChangeEquiv_tmul,
      QuadraticDescent.conjugate_smul conjugation _
        (SplitLaurentGalois.conjugate_algebraMap conjugation),
      show SplitLaurentGalois.conjugate conjugation (a : LaurentRing (K := E)) = a
        from a.property,
      map_smul, map_smul, extendPoint_fixed,
      QuadraticDescent.conjugate_smul conjugation _ (baseChangeConjugation_algebraMap A),
      CyclotomicScalarDescent.conjugation_one_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Equivariance is the exact condition for a split point to descend. -/
def IsEquivariant (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A) : Prop :=
  ∀ b, f (SplitLaurentGalois.conjugate conjugation b) = baseChangeConjugation A (f b)

private def fixedPoint (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A)
    (hf : IsEquivariant f) :
    coverFixedRing →ₐ[ℚ] QuadraticDescent.fixedRing (baseChangeConjugation A) :=
  ((f.restrictScalars ℚ).comp coverFixedRing.val).codRestrict _ (by
    intro b
    change baseChangeConjugation A (f (b : LaurentRing (K := E))) = f b
    rw [← hf, show SplitLaurentGalois.conjugate conjugation (b : LaurentRing (K := E)) = b
      from b.property])

/-- Descend an equivariant point by taking its fixed coefficient values. -/
def descendPoint (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A) (hf : IsEquivariant f) :
    coverFixedRing →ₐ[ℚ] A :=
  (CyclotomicScalarDescent.fixedEquiv A).symm.toAlgHom.comp (fixedPoint f hf)

@[simp]
theorem descendPoint_apply (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A)
    (hf : IsEquivariant f) (b : coverFixedRing) :
    (1 : E) ⊗ₜ[ℚ] descendPoint f hf b = f (b : LaurentRing (K := E)) :=
  congrArg Subtype.val ((CyclotomicScalarDescent.fixedEquiv A).apply_symm_apply (fixedPoint f hf b))

/-- Extension is uniquely determined by its values on the fixed ring. -/
theorem splitPoint_ext {f g : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A}
    (h : ∀ b : coverFixedRing, f (b : LaurentRing (K := E)) = g b) : f = g := by
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := coverBaseChangeEquiv.surjective b
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a => simp only [coverBaseChangeEquiv_tmul, map_smul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem extend_descend (f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A)
    (hf : IsEquivariant f) : extendPoint (descendPoint f hf) = f := by
  apply splitPoint_ext
  intro b
  rw [extendPoint_fixed, descendPoint_apply]

theorem descend_extend (f : coverFixedRing →ₐ[ℚ] A) :
    descendPoint (extendPoint f) (extendPoint_conjugate f) = f := by
  apply AlgHom.ext
  intro b
  apply CyclotomicScalarDescent.includeRight_injective A
  exact (descendPoint_apply _ _ b).trans (extendPoint_fixed f b)

theorem extendPoint_injective : Function.Injective (extendPoint (A := A)) := by
  intro f g h
  apply AlgHom.ext
  intro b
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] f b = (1 : E) ⊗ₜ[ℚ] g b
  rw [← extendPoint_fixed, ← extendPoint_fixed, h]

/-- Points of the fixed ring are precisely the equivariant split points. -/
def equivariantPointEquiv : (coverFixedRing →ₐ[ℚ] A) ≃
    {f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A // IsEquivariant f} where
  toFun f := ⟨extendPoint f, extendPoint_conjugate f⟩
  invFun f := descendPoint f.val f.property
  left_inv := descend_extend
  right_inv f := Subtype.ext (extend_descend f.val f.property)

/-- Extension of points is natural in the rational coefficient algebra. -/
theorem extendPoint_comp {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (f : coverFixedRing →ₐ[ℚ] A) :
    extendPoint (φ.comp f) =
      (Algebra.TensorProduct.map (AlgHom.id E E) φ).comp (extendPoint f) := by
  apply splitPoint_ext
  intro b
  simp only [extendPoint_fixed, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

end Cubic.QuadraticCorrespondence.CyclotomicPointDescent
