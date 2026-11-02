import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Topology.Constructions

/-!
# The topology on points given by regular functions

For an algebra `B` and a topological coefficient algebra `A`, give `B →ₐ[K] A`
the topology of pointwise evaluation. Thus a map into the point space is
continuous exactly when every regular function has continuous evaluation.
This definition uses only the coordinate algebra, not a parametrization.
-/

namespace Cubic.QuadraticCorrespondence.RegularFunctionTopology

variable {K B A : Type*} [CommSemiring K] [Semiring B] [Algebra K B]
  [Semiring A] [Algebra K A] [TopologicalSpace A]

/-- The topology on algebra-valued points induced by all regular functions. -/
scoped instance : TopologicalSpace (B →ₐ[K] A) :=
  TopologicalSpace.induced (fun f : B →ₐ[K] A => (f : B → A)) inferInstance

theorem isEmbedding_coe :
    Topology.IsEmbedding (fun f : B →ₐ[K] A => (f : B → A)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → (B →ₐ[K] A)) :
    Continuous f ↔ ∀ b, Continuous (fun x => f x b) := by
  rw [isEmbedding_coe.continuous_iff, continuous_pi_iff]
  rfl

theorem continuous_eval (b : B) : Continuous (fun f : B →ₐ[K] A => f b) :=
  (continuous_iff id).mp continuous_id b

/-- An isomorphism of coordinate algebras respects the topology on points. -/
def arrowHomeomorph {C : Type*} [Semiring C] [Algebra K C] (e : B ≃ₐ[K] C) :
    (B →ₐ[K] A) ≃ₜ (C →ₐ[K] A) where
  __ := e.arrowCongr (AlgEquiv.refl : A ≃ₐ[K] A)
  continuous_toFun := (continuous_iff _).mpr fun c => continuous_eval (e.symm c)
  continuous_invFun := (continuous_iff _).mpr fun b => continuous_eval (e b)

end Cubic.QuadraticCorrespondence.RegularFunctionTopology
