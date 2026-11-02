import Cubic.QuadraticCorrespondence.CyclotomicLocalTopology
import Cubic.QuadraticCorrespondence.CyclotomicScalarDescent
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The local tensor algebra in the paper's order

Equip `E ⊗[ℚ] A` with the module topology for its right `A`-action. The tensor
commutor identifies it continuously with the existing left-oriented local
algebra. Conjugation is continuous, and the scalar inclusion is a topological
embedding; the latter lets continuity descend back to the original points.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicTensorTopology

open CyclotomicField CyclotomicTorusGalois
open scoped TensorProduct CyclotomicBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A : Type*) [Field A] [CharZero A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The finite-dimensional module topology for the coefficient field on the right. -/
scoped instance : TopologicalSpace (E ⊗[ℚ] A) := moduleTopology A (E ⊗[ℚ] A)

scoped instance : IsModuleTopology A (E ⊗[ℚ] A) := ⟨rfl⟩

private instance finiteDimensional : FiniteDimensional A (E ⊗[ℚ] A) :=
  Module.Finite.equiv (Algebra.TensorProduct.commRight ℚ A E).toLinearEquiv

scoped instance : IsTopologicalRing (E ⊗[ℚ] A) :=
  IsModuleTopology.isTopologicalRing A (E ⊗[ℚ] A)

/-- Swapping tensor factors preserves the natural coefficient-field topology. -/
def commContinuousEquiv : (E ⊗[ℚ] A) ≃A[A] CyclotomicBaseChange.LocalAlgebra A where
  __ := (Algebra.TensorProduct.commRight ℚ A E).symm
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.commRight ℚ A E).symm.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.commRight ℚ A E).toLinearMap

/-- The same comparison on the topological unit groups. -/
def commUnitsEquiv : (E ⊗[ℚ] A)ˣ ≃ₜ* (CyclotomicBaseChange.LocalAlgebra A)ˣ :=
  Units.mapContinuousMulEquiv {
    __ := (commContinuousEquiv A).toAlgEquiv.toMulEquiv
    __ := (commContinuousEquiv A).toHomeomorph }

omit [IsTopologicalRing A] in
theorem continuous_tmul (c : E) : Continuous (fun a : A => c ⊗ₜ[ℚ] a) := by
  have hc : Continuous (fun a : A => a • (c ⊗ₜ[ℚ] (1 : A))) :=
    continuous_id.smul continuous_const
  convert hc using 1
  ext a
  simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem continuous_conjugation : Continuous (baseChangeConjugation A) := by
  let e : (E ⊗[ℚ] A) ≃ₐ[A] (E ⊗[ℚ] A) :=
    AlgEquiv.ofRingEquiv (f := (baseChangeConjugation A).toRingEquiv) (fun a => by
      change baseChangeConjugation A (1 ⊗ₜ[ℚ] a) = 1 ⊗ₜ[ℚ] a
      simp [baseChangeConjugation])
  exact IsModuleTopology.continuous_of_linearMap e.toLinearMap

/-- Scalar inclusion has a continuous linear left inverse. No local root or
coordinate parametrization enters this topological embedding. -/
theorem isEmbedding_includeRight :
    Topology.IsEmbedding (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A) := by
  let i : A →ₗ[A] E ⊗[ℚ] A := (Algebra.ofId A (E ⊗[ℚ] A)).toLinearMap
  have hi : Function.Injective i := CyclotomicScalarDescent.includeRight_injective A
  have hleft : Function.LeftInverse i.leftInverse i :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hi)
  exact hleft.isEmbedding (IsModuleTopology.continuous_of_linearMap i.leftInverse)
    (IsModuleTopology.continuous_of_linearMap i)

end Cubic.QuadraticCorrespondence.CyclotomicTensorTopology
