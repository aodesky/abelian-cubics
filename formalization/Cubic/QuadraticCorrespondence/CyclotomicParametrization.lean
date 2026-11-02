import CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
import Cubic.QuadraticCorrespondence.RationalCorrespondence

/-!
# The group-isomorphism clauses of the cyclotomic parametrization

These prove the specified natural group isomorphism and its canonicity up to
automorphisms of the full group functor. The remaining clauses of
`prop:cyclotomicParametrization` are proved in other modules and assembled in
`CyclotomicParametrizationAssembly`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicParametrization

open scoped TensorProduct RationalQuotientGroup
open CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
open CyclotomicField RationalQuotientGroup

/-- The specified isomorphism on all commutative rational coefficient algebras. -/
def specifiedIsomorphism : NaturalGroupIso where
  app := quotientRestrictionScalarsMulEquiv
  naturality := fun A _ _ _ _ _ φ p => quotientRestrictionScalarsMulEquiv_comp A φ p

/-- Changing the group-functor isomorphism gives a natural group automorphism. -/
def changeIsomorphism (ι κ : NaturalGroupIso) : NaturalUnitAutomorphism where
  app A := (ι.app A).symm.trans (κ.app A)
  naturality := by
    intro A B _ _ _ _ φ u
    have h : (ι.app B).symm
        (Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom u) =
          φ.comp ((ι.app A).symm u) := by
      apply (ι.app B).injective
      rw [MulEquiv.apply_symm_apply, ι.naturality, MulEquiv.apply_symm_apply]
    change κ.app B ((ι.app B).symm _) = _
    rw [h, κ.naturality]
    rfl

/-- Canonicity uses automorphisms of the whole algebraic-group functor. -/
theorem canonical_up_to_automorphism (ι κ : NaturalGroupIso) :
    ∃ α : NaturalUnitAutomorphism, ∀ (A : Type) [CommRing A] [Algebra ℚ A] (p : Points A),
      κ.app A p = α.app A (ι.app A p) := by
  refine ⟨changeIsomorphism ι κ, ?_⟩
  intro A _ _ p
  exact congrArg (κ.app A) ((ι.app A).symm_apply_apply p).symm

/-- The rational map is precisely the parameter used in the proved coefficient formulas. -/
theorem rationalEquiv_specified (p : Points ℚ) :
    rationalEquiv specifiedIsomorphism p = RationalCoefficientFormula.parameterEquiv p := rfl

end Cubic.QuadraticCorrespondence.CyclotomicParametrization
