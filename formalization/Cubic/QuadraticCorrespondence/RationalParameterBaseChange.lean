import Cubic.QuadraticCorrespondence.RationalQuotientGroup

/-!
# Base change of the rational cyclotomic parameter

Identify the specified rational group parametrization with `Eˣ` and prove its
compatibility with the original point functor at every rational coefficient
algebra. Local arithmetic can then be transferred to the rational
diagonal, without selecting a cover lift.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalParameterBaseChange

open CyclotomicField CyclotomicTorusGalois RationalQuotientGroup
open scoped TensorProduct RationalQuotientGroup

def parameterEquiv : (quotientFixedRing →ₐ[ℚ] ℚ) ≃* Eˣ :=
  (quotientRestrictionScalarsMulEquiv ℚ).trans
    (Units.mapEquiv (Algebra.TensorProduct.rid ℚ E E).toMulEquiv)

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The global field enters a scalar extension through the specified left tensor factor. -/
def fieldInclusion : E →ₐ[ℚ] E ⊗[ℚ] A :=
  (Algebra.TensorProduct.includeLeft : E →ₐ[E] E ⊗[ℚ] A).restrictScalars ℚ

theorem tensor_map_eq (x : E ⊗[ℚ] ℚ) :
    Algebra.TensorProduct.map (AlgHom.id E E) (Algebra.ofId ℚ A) x =
      fieldInclusion A (Algebra.TensorProduct.rid ℚ E E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a q =>
    simp [fieldInclusion, Algebra.TensorProduct.rid_tmul,
      TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp [hx, hy]

/-- Naturality on the full rational point group, not only the image of rational cover points. -/
theorem parameter_baseChange (P : quotientFixedRing →ₐ[ℚ] ℚ) :
    quotientRestrictionScalarsMulEquiv A ((Algebra.ofId ℚ A).comp P) =
      Units.map (fieldInclusion A).toMonoidHom (parameterEquiv P) := by
  rw [quotientRestrictionScalarsMulEquiv_comp]
  apply Units.ext
  exact tensor_map_eq A _

theorem parameter_baseChange_val (P : quotientFixedRing →ₐ[ℚ] ℚ) :
    (quotientRestrictionScalarsMulEquiv A ((Algebra.ofId ℚ A).comp P) : E ⊗[ℚ] A) =
      fieldInclusion A (parameterEquiv P : E) :=
  congrArg Units.val (parameter_baseChange A P)

/-- The rational coefficients in the cyclotomic basis are unchanged by any local realization. -/
theorem map_parameter_linear {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : E ⊗[ℚ] A →ₐ[ℚ] B) (P : quotientFixedRing →ₐ[ℚ] ℚ) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta) :
    f (quotientRestrictionScalarsMulEquiv A ((Algebra.ofId ℚ A).comp P)) =
      algebraMap ℚ B a + algebraMap ℚ B b * f (zeta ⊗ₜ[ℚ] (1 : A)) := by
  rw [parameter_baseChange_val, hP]
  simp only [map_add, map_mul, AlgHom.commutes]
  rfl

end Cubic.QuadraticCorrespondence.RationalParameterBaseChange
