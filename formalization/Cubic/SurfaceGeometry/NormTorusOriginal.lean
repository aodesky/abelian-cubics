import Cubic.SurfaceGeometry.NormTorus
import Cubic.QuadraticCorrespondence.RationalQuotientGroup
import Mathlib.Tactic.Group

noncomputable section

namespace Cubic.SurfaceGeometry.NormTorusOriginal

open RationalFormData Cubic.QuadraticCorrespondence
open CyclotomicField CyclotomicTorusGalois RationalQuotientGroup
open scoped TensorProduct RationalQuotientGroup

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- Comparison with the original descended invariant Laurent ring, using its
specified quotient-character basis. -/
def equivalence : TorusChart R ≃ (quotientFixedRing →ₐ[ℚ] R) :=
  (NormTorus.equivalence R).trans (quotientRestrictionScalarsMulEquiv R).toEquiv.symm

theorem parameter (x : TorusChart R) :
    quotientRestrictionScalarsMulEquiv R (equivalence R x) = NormTorus.equivalence R x :=
  (quotientRestrictionScalarsMulEquiv R).apply_symm_apply _

theorem value (x : TorusChart R) :
    (quotientRestrictionScalarsMulEquiv R (equivalence R x) : E ⊗[ℚ] R) =
      quadraticElement (x.val 1) (x.val 2) := by
  rw [parameter,NormTorus.equivalence_value]

theorem multiplication (x y z : TorusChart R) (hz : z.val=torusProduct x.val y.val) :
    equivalence R z = equivalence R x * equivalence R y := by
  apply (quotientRestrictionScalarsMulEquiv R).injective
  rw [map_mul,parameter,parameter,parameter]
  exact NormTorus.equivalence_mul R x y z hz

theorem natural {S : Type*} [CommRing S] [Algebra ℚ S]
    (φ : R →ₐ[ℚ] S) (x : TorusChart R) :
    equivalence S (NormTorus.mapPoint R φ x) = φ.comp (equivalence R x) := by
  apply (quotientRestrictionScalarsMulEquiv S).injective
  rw [quotientRestrictionScalarsMulEquiv_comp,parameter,parameter]
  exact NormTorus.equivalence_natural R φ x

/-- The two ratios ℓ₁³/(ℓ₀ℓ₁ℓ₂), ℓ₂³/(ℓ₀ℓ₁ℓ₂) have precisely
the pullbacks of the original quotient-character basis, after ℓ₀=1. -/
theorem character_basis : CharacterLattice.pullback (1,0) = (2,-1) ∧
    CharacterLattice.pullback (0,1) = (-1,2) := by decide

omit [Algebra ℚ R] in
theorem character_ratios (s t : Rˣ) :
    s^3/(s*t)=s^2/t ∧ t^3/(s*t)=t^2/s := by
  constructor
  · rw [pow_succ,mul_comm s t]
    exact mul_div_mul_right_eq_div (s^2) t s
  · rw [pow_succ]
    exact mul_div_mul_right_eq_div (t^2) s t

omit [Algebra ℚ R] in
theorem normalized_equation (x : Fin 3 → R) :
    CubicData.normCubic ![x 0,x 1,x 2,1] = 0 ↔ x 0*(x 1^2+3*x 2^2)=1 := by
  simp [CubicData.normCubic,sub_eq_zero]

end Cubic.SurfaceGeometry.NormTorusOriginal
