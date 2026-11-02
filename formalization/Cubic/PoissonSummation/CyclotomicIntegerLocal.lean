import Cubic.PoissonSummation.CyclotomicIntegerUnits
import Cubic.QuadraticCorrespondence.CyclotomicBaseChange
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedIntegers

/-!
# Compatibility of global integers with the local field at three

The reduction on global units used in the compact-quotient argument is the
restriction of the specified global-to-local field map. This compatibility
prevents the finite six-unit calculation from replacing the paper's actual map.
-/

noncomputable section

namespace Cubic.PoissonSummation.CyclotomicIntegerUnits

open NumberField Polynomial
open Cubic.QuadraticCorrespondence CyclotomicField

/-- Scalar extension of the specified global cyclotomic presentation. -/
def toLocalField : E →ₐ[ℚ] CyclotomicRamifiedField.Extension :=
  (CyclotomicBaseChange.scalarExtension ℚ_[3]).comp presentation.symm.toAlgHom

@[simp]
theorem toLocalField_zeta : toLocalField zeta = CyclotomicRamifiedField.zeta := by
  have h := presentation.symm_apply_eq.mpr presentation_root.symm
  change CyclotomicBaseChange.scalarExtension ℚ_[3] (presentation.symm zeta) = _
  rw [h, CyclotomicBaseChange.scalarExtension_root]
  rfl

theorem integralEmbedding_toLocalOrder (x : Integers) :
    CyclotomicRamifiedField.integralEmbedding (toLocalOrder x) =
      toLocalField (x : E) := by
  let f : Integers →ₐ[ℤ] CyclotomicRamifiedField.Extension :=
    (CyclotomicRamifiedField.integralEmbedding.comp toLocalOrder.toRingHom).toIntAlgHom
  let g : Integers →ₐ[ℤ] CyclotomicRamifiedField.Extension :=
    (toLocalField.toRingHom.comp (algebraMap Integers E)).toIntAlgHom
  have h : f = g := integralPowerBasis.algHom_ext (by
    rw [integralPowerBasis_gen]
    change CyclotomicRamifiedField.integralEmbedding (toLocalOrder zetaInteger) =
      toLocalField zeta
    rw [toLocalOrder_zeta, CyclotomicRamifiedField.integralEmbedding_zeta, toLocalField_zeta])
  exact DFunLike.congr_fun h x

theorem toLocalOrder_injective : Function.Injective toLocalOrder := by
  intro x y h
  apply (show Function.Injective (algebraMap Integers E) from Subtype.val_injective)
  apply toLocalField.injective
  simpa only [integralEmbedding_toLocalOrder] using
    congrArg CyclotomicRamifiedField.integralEmbedding h

/-- At any multiplicatively normed realization, global units have absolute value one. -/
theorem norm_unit_image {F : Type*} [NormedField F] (f : Integers →+* F) (u : Integersˣ) :
    ‖f (u : Integers)‖ = 1 := by
  have h : (u : Integers) ^ 6 = 1 := congrArg Units.val (unit_pow_six u)
  have hi : f (u : Integers) ^ 6 = 1 := by simpa using congrArg f h
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm hi

end Cubic.PoissonSummation.CyclotomicIntegerUnits
