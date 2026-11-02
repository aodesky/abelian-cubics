import Cubic.QuadraticCorrespondence.CyclotomicTensorTopology
import Cubic.QuadraticCorrespondence.SplitLaurentTopology
import Cubic.QuadraticCorrespondence.RationalQuotientGroup

/-!
# Local topology of the original descended quotient

The original quotient points have the topology induced by evaluation of all
regular functions. The cyclotomic tensor has its coefficient-field module
topology. We prove that the specified algebraic parametrization is a
homeomorphism for these topologies. This is used to transfer Haar measure and
local Fourier integrals.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientLocalTopology

open CyclotomicField CyclotomicTorusGalois CyclotomicTorusDescent
open CyclotomicPointDescent CyclotomicRestrictionScalars RationalQuotientGroup
open SplitLaurentInvariants SplitLaurentEvaluation SplitLaurentPoints
open scoped TensorProduct RegularFunctionTopology CyclotomicTensorTopology RationalQuotientGroup

variable (A : Type*) [Field A] [CharZero A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Extending a point is continuous on every fixed Laurent polynomial. -/
theorem continuous_extendPoint_eval (b : LaurentRing (K := E)) :
    Continuous (fun P : coverFixedRing →ₐ[ℚ] A => extendPoint P b) := by
  obtain ⟨x, rfl⟩ := coverBaseChangeEquiv.surjective b
  induction x using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ => (0 : E ⊗[ℚ] A)))
  | tmul c a =>
    have h : ∀ P : coverFixedRing →ₐ[ℚ] A,
        extendPoint P (coverBaseChangeEquiv (c ⊗ₜ[ℚ] a)) = c ⊗ₜ[ℚ] P a := by
      intro P
      change (Algebra.TensorProduct.map (AlgHom.id E E) P)
        (coverBaseChangeEquiv.symm (coverBaseChangeEquiv (c ⊗ₜ[ℚ] a))) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
    simp_rw [h]
    exact (CyclotomicTensorTopology.continuous_tmul A c).comp
      (RegularFunctionTopology.continuous_eval a)
  | add x y hx hy => simpa only [map_add] using hx.add hy

theorem continuous_restrictionScalars : Continuous (restrictionScalarsEquiv A) := by
  change Continuous (fun P : coverFixedRing →ₐ[ℚ] A => (coordinates (extendPoint P)).1)
  apply Units.continuous_iff.mpr
  exact ⟨continuous_extendPoint_eval A _, continuous_extendPoint_eval A _⟩

theorem continuous_restrictionScalars_symm : Continuous (restrictionScalarsEquiv A).symm := by
  apply (RegularFunctionTopology.continuous_iff _).mpr
  intro b
  apply (CyclotomicTensorTopology.isEmbedding_includeRight A).continuous_iff.mpr
  have h : ∀ u : (E ⊗[ℚ] A)ˣ,
      (1 : E) ⊗ₜ[ℚ] (restrictionScalarsEquiv A).symm u b =
        evaluate (u, conjugateUnit A u) (b : LaurentRing (K := E)) := by
    intro u
    exact descendPoint_apply _ _ b
  change Continuous (fun u => (1 : E) ⊗ₜ[ℚ] (restrictionScalarsEquiv A).symm u b)
  simp_rw [h]
  exact (SplitLaurentTopology.continuous_evaluate (b : LaurentRing (K := E))).comp
    (continuous_id.prodMk ((CyclotomicTensorTopology.continuous_conjugation A).units_map
      (baseChangeConjugation A).toMonoidHom))

/-- The descended Laurent point parametrization preserves the evaluation topology. -/
def restrictionScalarsHomeomorph : (coverFixedRing →ₐ[ℚ] A) ≃ₜ (E ⊗[ℚ] A)ˣ where
  __ := restrictionScalarsEquiv A
  continuous_toFun := continuous_restrictionScalars A
  continuous_invFun := continuous_restrictionScalars_symm A

/-- The original cyclic quotient, with its regular-function topology, is
topologically isomorphic to the local cyclotomic unit group. -/
def quotientRestrictionScalarsContinuousMulEquiv :
    (quotientFixedRing →ₐ[ℚ] A) ≃ₜ* (E ⊗[ℚ] A)ˣ where
  __ := quotientRestrictionScalarsMulEquiv A
  __ := (RegularFunctionTopology.arrowHomeomorph fixedRingEquiv.symm).trans
    (restrictionScalarsHomeomorph A)

@[simp]
theorem quotientRestrictionScalarsContinuousMulEquiv_apply
    (P : quotientFixedRing →ₐ[ℚ] A) :
    quotientRestrictionScalarsContinuousMulEquiv A P = quotientRestrictionScalarsEquiv A P := rfl

/-- Continuity of the descended group law in the regular-function topology. -/
scoped instance : IsTopologicalGroup (quotientFixedRing →ₐ[ℚ] A) :=
  (quotientRestrictionScalarsContinuousMulEquiv A).toHomeomorph.isInducing.topologicalGroup
    (quotientRestrictionScalarsMulEquiv A)

end Cubic.QuadraticCorrespondence.QuotientLocalTopology
