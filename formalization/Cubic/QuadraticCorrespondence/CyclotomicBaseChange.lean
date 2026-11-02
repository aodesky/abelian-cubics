import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of the quadratic cyclotomic field

Identify `K ⊗[ℚ] E` with `K[X]/(X²+X+1)`. The order of the tensor factors
places the scalar field on the left, as in mathlib's base-change API. The maps
are specified on the cyclotomic generator, rather than chosen by dimension.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicBaseChange

open Polynomial CyclotomicLocalAlgebra
open scoped TensorProduct

variable (K : Type*) [Field K] [CharZero K]

/-- The coefficient-extension map preserves the quotient generator. -/
def scalarExtension : Model ℚ →ₐ[ℚ] Model K :=
  AdjoinRoot.mapAlgHom (Algebra.ofId ℚ K) (cyclotomic 3 ℚ) (cyclotomic 3 K)
    (by simp)

@[simp]
theorem scalarExtension_root : scalarExtension K (AdjoinRoot.root (cyclotomic 3 ℚ)) =
    AdjoinRoot.root (cyclotomic 3 K) := by
  simp [scalarExtension]

/-- Multiplication of the scalar and cyclotomic factors in the local quotient. -/
def quotientBaseChangeHom : K ⊗[ℚ] Model ℚ →ₐ[K] Model K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (Model K)) (scalarExtension K)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem quotientBaseChangeHom_tmul (a : K) (b : Model ℚ) :
    quotientBaseChangeHom K (a ⊗ₜ[ℚ] b) = algebraMap K (Model K) a * scalarExtension K b := rfl

private theorem tensor_root_relation :
    (1 ⊗ₜ[ℚ] AdjoinRoot.root (cyclotomic 3 ℚ) : K ⊗[ℚ] Model ℚ) ^ 2 +
      1 ⊗ₜ[ℚ] AdjoinRoot.root (cyclotomic 3 ℚ) + 1 = 0 := by
  have h : (AdjoinRoot.root (cyclotomic 3 ℚ)) ^ 2 +
      AdjoinRoot.root (cyclotomic 3 ℚ) + 1 = 0 := by
    simpa [cyclotomic_three] using AdjoinRoot.eval₂_root (cyclotomic 3 ℚ)
  simpa only [map_add, map_pow, map_one, map_zero,
    Algebra.TensorProduct.includeRight_apply] using
    congrArg (Algebra.TensorProduct.includeRight : Model ℚ →ₐ[ℚ] K ⊗[ℚ] Model ℚ) h

/-- The tensor of the global root satisfies the defining local polynomial. -/
def quotientBaseChangeInverse : Model K →ₐ[K] K ⊗[ℚ] Model ℚ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) (1 ⊗ₜ[ℚ] AdjoinRoot.root (cyclotomic 3 ℚ))
    (by simpa [cyclotomic_three] using tensor_root_relation K)

@[simp]
theorem quotientBaseChangeInverse_root :
    quotientBaseChangeInverse K (AdjoinRoot.root (cyclotomic 3 K)) =
      1 ⊗ₜ[ℚ] AdjoinRoot.root (cyclotomic 3 ℚ) := by
  simp [quotientBaseChangeInverse]

private theorem hom_comp_inverse :
    (quotientBaseChangeHom K).comp (quotientBaseChangeInverse K) = .id K (Model K) := by
  apply AdjoinRoot.algHom_ext
  simp

private theorem inverse_comp_hom :
    (quotientBaseChangeInverse K).comp (quotientBaseChangeHom K) =
      .id K (K ⊗[ℚ] Model ℚ) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AdjoinRoot.algHom_ext
    simp

/-- Base change commutes with this polynomial-quotient presentation. -/
def quotientBaseChange : K ⊗[ℚ] Model ℚ ≃ₐ[K] Model K :=
  AlgEquiv.ofAlgHom (quotientBaseChangeHom K) (quotientBaseChangeInverse K)
    (hom_comp_inverse K) (inverse_comp_hom K)

@[simp]
theorem quotientBaseChange_tmul (a : K) (b : Model ℚ) :
    quotientBaseChange K (a ⊗ₜ[ℚ] b) = algebraMap K (Model K) a * scalarExtension K b := rfl

/-- The base-changed global field, before choosing any local splitting. -/
abbrev LocalAlgebra := K ⊗[ℚ] CyclotomicField.E

/-- The global field's local tensor algebra is the cyclotomic quotient used in
the split-place calculation. -/
def presentation : LocalAlgebra K ≃ₐ[K] Model K :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
    CyclotomicField.presentation.symm).trans (quotientBaseChange K)

@[simp]
theorem presentation_zeta :
    presentation K (1 ⊗ₜ[ℚ] CyclotomicField.zeta) = AdjoinRoot.root (cyclotomic 3 K) := by
  have h : CyclotomicField.presentation.symm CyclotomicField.zeta =
      AdjoinRoot.root (cyclotomic 3 ℚ) :=
    CyclotomicField.presentation.symm_apply_eq.mpr CyclotomicField.presentation_root.symm
  simp [presentation, Algebra.TensorProduct.congr, h]

/-- The same presentation with the tensor factors in the paper's order.
The canonical tensor commutor relates it to the `K`-algebra used above. -/
def paperPresentation : CyclotomicField.E ⊗[ℚ] K ≃ₐ[ℚ] Model K :=
  (Algebra.TensorProduct.comm ℚ CyclotomicField.E K).trans
    ((presentation K).restrictScalars ℚ)

@[simp]
theorem paperPresentation_zeta :
    paperPresentation K (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : K)) =
      AdjoinRoot.root (cyclotomic 3 K) := by
  simp [paperPresentation]

end Cubic.QuadraticCorrespondence.CyclotomicBaseChange
