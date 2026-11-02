import Cubic.QuadraticCorrespondence.CyclotomicScalarDescent

/-!
# Descent of the original augmentation-one units

Change of coefficients from `A` to `E ⊗[ℚ] A` identifies the original
augmentation-one units with the units fixed by coefficient conjugation.
Both the group-algebra element and its inverse descend, so no assumption
that a quotient point lifts to the cover enters this construction.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicCoverDescent

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois
open Cubic.OrbitParametrization.CyclicGroupAlgebra

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Extension of coefficients on the original convolution algebra. -/
def coefficientMap : GroupAlgebra A →+* GroupAlgebra (E ⊗[ℚ] A) :=
  AddMonoidAlgebra.mapRangeRingHom (ZMod 3)
    (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A).toRingHom

@[simp]
theorem coefficientMap_apply (f : GroupAlgebra A) (i : ZMod 3) :
    coefficientMap A f i = (1 : E) ⊗ₜ[ℚ] f i := rfl

theorem coefficientMap_injective : Function.Injective (coefficientMap A) := by
  intro f g h
  ext i
  apply CyclotomicScalarDescent.includeRight_injective A
  exact congrArg (fun a : GroupAlgebra (E ⊗[ℚ] A) => a i) h

/-- Fixed convolution coefficients all descend to the rational coefficient algebra. -/
theorem exists_coefficient_preimage (f : GroupAlgebra (E ⊗[ℚ] A))
    (hf : ∀ i, baseChangeConjugation A (f i) = f i) :
    ∃ g : GroupAlgebra A, coefficientMap A g = f := by
  let g : GroupAlgebra A := Finsupp.equivFunOnFinite.symm
    (fun i => (CyclotomicScalarDescent.fixedEquiv A).symm ⟨f i, hf i⟩)
  refine ⟨g, ?_⟩
  ext i
  exact congrArg Subtype.val
    ((CyclotomicScalarDescent.fixedEquiv A).apply_symm_apply ⟨f i, hf i⟩)

/-- The original cover's extension-of-coefficients homomorphism. -/
def extendCover : traceOneUnits A →* traceOneUnits (E ⊗[ℚ] A) :=
  mapUnits (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A).toRingHom

theorem extendCover_injective : Function.Injective (extendCover A) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  apply coefficientMap_injective A
  exact congrArg (fun u : traceOneUnits (E ⊗[ℚ] A) => (u.val : GroupAlgebra (E ⊗[ℚ] A))) he

theorem extendCover_fixed (g : traceOneUnits A) :
    mapUnits (baseChangeConjugation A).toRingHom (extendCover A g) = extendCover A g := by
  apply Subtype.ext
  apply Units.ext
  ext i
  simp only [extendCover, mapUnits_coefficient]
  exact CyclotomicScalarDescent.conjugation_one_tmul A _

/-- A fixed unit descends together with its inverse and augmentation equation. -/
theorem exists_cover_preimage (g : traceOneUnits (E ⊗[ℚ] A))
    (hg : mapUnits (baseChangeConjugation A).toRingHom g = g) :
    ∃ h : traceOneUnits A, extendCover A h = g := by
  have hgcoeff : ∀ i, baseChangeConjugation A ((g.val : GroupAlgebra (E ⊗[ℚ] A)) i) =
      (g.val : GroupAlgebra (E ⊗[ℚ] A)) i := by
    intro i
    exact congrArg (fun u : traceOneUnits (E ⊗[ℚ] A) =>
      (u.val : GroupAlgebra (E ⊗[ℚ] A)) i) hg
  have hginv : mapUnits (baseChangeConjugation A).toRingHom g⁻¹ = g⁻¹ := by
    rw [map_inv, hg]
  have hicoeff : ∀ i, baseChangeConjugation A (((g⁻¹).val : GroupAlgebra (E ⊗[ℚ] A)) i) =
      ((g⁻¹).val : GroupAlgebra (E ⊗[ℚ] A)) i := by
    intro i
    exact congrArg (fun u : traceOneUnits (E ⊗[ℚ] A) =>
      (u.val : GroupAlgebra (E ⊗[ℚ] A)) i) hginv
  obtain ⟨a, ha⟩ := exists_coefficient_preimage A (g.val : GroupAlgebra (E ⊗[ℚ] A)) hgcoeff
  obtain ⟨b, hb⟩ := exists_coefficient_preimage A ((g⁻¹).val : GroupAlgebra (E ⊗[ℚ] A)) hicoeff
  let u : (GroupAlgebra A)ˣ :=
    { val := a
      inv := b
      val_inv := by
        apply coefficientMap_injective A
        rw [map_mul, ha, hb, map_one]
        exact Units.val_inv g.val
      inv_val := by
        apply coefficientMap_injective A
        rw [map_mul, hb, ha, map_one]
        exact Units.inv_val g.val }
  have hu : u ∈ traceOneUnits A := by
    apply Units.ext
    change augmentation A a = 1
    apply CyclotomicScalarDescent.includeRight_injective A
    change (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A) (augmentation A a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A) 1
    have he := augmentation_mapRange
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A).toRingHom a
    change augmentation (E ⊗[ℚ] A) (coefficientMap A a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A) (augmentation A a) at he
    rw [← he, ha, augmentation_traceOneUnit, map_one]
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact ha

/-- The fixed subgroup is the image of the original rational cover functor. -/
def fixedCover : Subgroup (traceOneUnits (E ⊗[ℚ] A)) :=
  (mapUnits (baseChangeConjugation A).toRingHom).eqLocus (MonoidHom.id _)

/-- Descent is a group isomorphism, not only a correspondence between values. -/
def fixedCoverEquiv : traceOneUnits A ≃* fixedCover A :=
  MulEquiv.ofBijective ((extendCover A).codRestrict (fixedCover A) (extendCover_fixed A))
    ⟨fun _ _ h => extendCover_injective A (congrArg Subtype.val h), by
      intro g
      obtain ⟨h, hh⟩ := exists_cover_preimage A g.val g.property
      exact ⟨h, Subtype.ext hh⟩⟩

/-- Change of coefficients commutes with scalar extension on the original cover. -/
theorem extendCover_mapUnits {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (g : traceOneUnits A) :
    extendCover A' (mapUnits φ.toRingHom g) =
      mapUnits (Algebra.TensorProduct.map (AlgHom.id E E) φ).toRingHom (extendCover A g) := by
  apply Subtype.ext
  apply Units.ext
  ext i
  simp only [extendCover, mapUnits_coefficient]
  rfl

end Cubic.QuadraticCorrespondence.CyclotomicCoverDescent
