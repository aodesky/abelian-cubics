import Cubic.SurfaceGeometry.InvariantOrbitBasis
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section

namespace Cubic.SurfaceGeometry.InvariantBaseChangeData

open MvPolynomial InvariantOrbitBasis
open scoped TensorProduct

variable (R : Type*) [CommRing R]

/-- Extend the coefficients of an integral invariant polynomial to `R`. -/
def coefficientMap : invariantRing ℤ →ₐ[ℤ] invariantRing R :=
  (((mapAlgHom (Algebra.ofId ℤ R)).comp (invariantRing ℤ).val).codRestrict
    ((invariantRing R).restrictScalars ℤ) fun f => by
      change rename (finRotate 3) (map (Int.castRingHom R) f.val) =
        map (Int.castRingHom R) f.val
      rw [← map_rename]
      exact congrArg (map (Int.castRingHom R)) f.property)

theorem coefficientMap_val (f : invariantRing ℤ) :
    (coefficientMap R f).val = map (Int.castRingHom R) f.val := rfl

/-- The canonical change-of-coefficients homomorphism, not an isomorphism
chosen from abstract ranks. -/
def baseChange : R ⊗[ℤ] invariantRing ℤ →ₐ[R] invariantRing R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (invariantRing R))
    (coefficientMap R) (fun _ _ => Commute.all _ _)

theorem baseChange_tmul (r : R) (f : invariantRing ℤ) :
    baseChange R (r ⊗ₜ[ℤ] f) = r • coefficientMap R f := by
  rw [baseChange, Algebra.TensorProduct.lift_tmul]
  exact (Algebra.smul_def r (coefficientMap R f)).symm

end Cubic.SurfaceGeometry.InvariantBaseChangeData
