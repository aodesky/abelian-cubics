import Cubic.SurfaceGeometry.InvariantBaseChangeData
import Cubic.SurfaceGeometry.InvariantFibres

/-! The paper's orbit-sum argument for change of coefficients. The canonical
tensor map sends each integral orbit sum to the corresponding orbit sum over
the new coefficient ring, hence is an algebra isomorphism. -/

noncomputable section

namespace Cubic.SurfaceGeometry.InvariantBaseChange

open MvPolynomial InvariantOrbitBasis InvariantBaseChangeData CyclicMonomialOrbits
open scoped TensorProduct Classical

variable (R : Type*) [CommRing R]

theorem coefficientMap_basis (b : Orbit) :
    coefficientMap R (basis ℤ b) = basis R b := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  rw [coefficientMap_val, coeff_map, basis_coeff, basis_coeff]
  split_ifs <;> simp

theorem baseChange_bijective : Function.Bijective (baseChange R) := by
  let e := ((basis ℤ).baseChange R).equiv (basis R) (Equiv.refl Orbit)
  have he : (baseChange R).toLinearMap = e.toLinearMap := by
    apply ((basis ℤ).baseChange R).ext
    intro b
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [Module.Basis.baseChange_apply, AlgHom.toLinearMap_apply,
      baseChange_tmul, coefficientMap_basis, one_smul, Equiv.refl_apply]
  have hf : (baseChange R : _ → invariantRing R) = e :=
    congrArg (fun f : (R ⊗[ℤ] invariantRing ℤ) →ₗ[R] invariantRing R => (f : _ → _)) he
  rw [hf]
  exact e.bijective

/-- Canonical `R ⊗ ℤ[X,Y,Z]^C₃ ≃ R[X,Y,Z]^C₃`, for every commutative ring `R`. -/
def presentation : R ⊗[ℤ] invariantRing ℤ ≃ₐ[R] invariantRing R :=
  AlgEquiv.ofBijective (baseChange R) (baseChange_bijective R)

theorem presentation_tmul (r : R) (f : invariantRing ℤ) :
    presentation R (r ⊗ₜ[ℤ] f) = r • coefficientMap R f :=
  baseChange_tmul R r f

/-- Every field fiber of the original invariant ring is normal. The field is
arbitrary, so this includes every field extension and characteristic three. -/
theorem tensor_invariants_normal (k : Type*) [Field k] :
    IsIntegrallyClosed (k ⊗[ℤ] Cubic.ToricHeights.TernaryCyclicInvariants.invariants) := by
  haveI : IsIntegrallyClosed (invariantRing k) := InvariantFibres.field_invariants_normal k
  exact IsIntegrallyClosed.of_equiv (presentation k).symm.toRingEquiv

end Cubic.SurfaceGeometry.InvariantBaseChange
