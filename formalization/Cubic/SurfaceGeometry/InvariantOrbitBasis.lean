import Cubic.SurfaceGeometry.OrbitCoefficientBasis
import Cubic.SurfaceGeometry.CyclicMonomialOrbits

noncomputable section

namespace Cubic.SurfaceGeometry.InvariantOrbitBasis

open MvPolynomial CyclicMonomialOrbits
open scoped Classical

variable (R : Type*) [CommRing R]

def invariantRing : Subalgebra R (MvPolynomial (Fin 3) R) :=
  AlgHom.equalizer (rename (finRotate 3)) (AlgHom.id R _)

/-- Coefficients of an invariant polynomial are precisely the finitely
supported functions constant on monomial orbits. -/
def coefficientsEquiv : invariantRing R ≃ₗ[R]
    OrbitCoefficientBasis.constantOnFibres R projection where
  toFun f := ⟨f.val, (invariant_iff_coefficients f.val).mp f.property⟩
  invFun f := ⟨f.val, (invariant_iff_coefficients f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual orbit-sum basis, over an arbitrary coefficient ring. -/
def basis : Module.Basis Orbit R (invariantRing R) :=
  (OrbitCoefficientBasis.basis R projection projection_surjective finite_fibres).map
    (coefficientsEquiv R).symm

theorem basis_coeff (b : Orbit) (d : Exponent) :
    (basis R b).val.coeff d = if projection d = b then 1 else 0 := by
  change (OrbitCoefficientBasis.basis R projection projection_surjective finite_fibres b).val d = _
  exact OrbitCoefficientBasis.basis_apply R projection projection_surjective finite_fibres b d

end Cubic.SurfaceGeometry.InvariantOrbitBasis
