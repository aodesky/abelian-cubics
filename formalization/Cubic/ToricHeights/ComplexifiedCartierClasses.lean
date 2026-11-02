import Cubic.ToricHeights.IntegralCartierClasses
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Complexification of the integral Cartier class lattice

The integral class quotient (`IntegralCartierClasses`) is computed from local
characters on the fan. Here we extend that quotient to complex scalars. Its
primitive positive generator is the anticanonical class; the paper assigns that
generator the coordinate three. The comparison with the complex
character-divisor quotient of `DivisorParameters` is proved on every integral
divisor, so this is the scalar extension of the integral calculation.
-/

noncomputable section

namespace Cubic.ToricHeights.ComplexifiedCartierClasses

open DivisorParameters IntegralCartierClasses
open scoped TensorProduct

abbrev ComplexifiedClass := ℂ ⊗[ℤ] IntegralClass

/-- Coordinate with the computed integral generator assigned one. -/
def primitiveCoordinate : ComplexifiedClass ≃ₗ[ℂ] ℂ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
    integralGeneratorEquiv.symm).trans (TensorProduct.AlgebraTensorModule.rid ℤ ℂ ℂ)

@[simp]
theorem primitiveCoordinate_tmul (c : ℂ) (x : IntegralClass) :
    primitiveCoordinate (c ⊗ₜ[ℤ] x) = (integralGeneratorEquiv.symm x : ℂ) * c := by
  simp [primitiveCoordinate, zsmul_eq_mul]

/-- The paper's scalar coordinate sends the primitive ample generator to three. -/
def normalizedCoordinate : ComplexifiedClass ≃ₗ[ℂ] ℂ :=
  primitiveCoordinate.trans (LinearEquiv.smulOfNeZero ℂ ℂ (3 : ℂ) (by norm_num))

theorem normalizedCoordinate_apply (x : ComplexifiedClass) :
    normalizedCoordinate x = 3 * primitiveCoordinate x := rfl

theorem integral_parameter (d : cartierDivisors) :
    3 * (integralGeneratorEquiv.symm (integralClassOf d) : ℂ) =
      (d.val.1 : ℂ) + 2 * d.val.2 := by
  have h := rational_parameter_generator (integralGeneratorEquiv.symm (integralClassOf d))
  rw [integralGeneratorEquiv.apply_symm_apply, toRationalClass_mk,
    classParameter_classOf] at h
  change (d.val.1 : ℚ) + 2 * d.val.2 =
    3 * (integralGeneratorEquiv.symm (integralClassOf d) : ℚ) at h
  exact_mod_cast h.symm

theorem normalizedCoordinate_integral (c : ℂ) (d : cartierDivisors) :
    normalizedCoordinate (c ⊗ₜ[ℤ] integralClassOf d) =
      c * ((d.val.1 : ℂ) + 2 * d.val.2) := by
  rw [normalizedCoordinate_apply, primitiveCoordinate_tmul, ← integral_parameter]
  ring

theorem normalizedCoordinate_anticanonical :
    normalizedCoordinate ((1 : ℂ) ⊗ₜ[ℤ] anticanonicalClass) = 3 := by
  change normalizedCoordinate ((1 : ℂ) ⊗ₜ[ℤ] integralClassOf anticanonical) = 3
  rw [normalizedCoordinate_integral]
  norm_num [anticanonical]

theorem primitiveCoordinate_anticanonical :
    primitiveCoordinate ((1 : ℂ) ⊗ₜ[ℤ] anticanonicalClass) = 1 := by
  have he : integralGeneratorEquiv 1 = anticanonicalClass := by
    change (1 : ℤ) • anticanonicalClass = anticanonicalClass
    exact one_smul ℤ _
  rw [primitiveCoordinate_tmul, ← he, integralGeneratorEquiv.symm_apply_apply]
  norm_num

theorem eq_smul_anticanonical (x : ComplexifiedClass) :
    x = primitiveCoordinate x • ((1 : ℂ) ⊗ₜ[ℤ] anticanonicalClass) := by
  apply primitiveCoordinate.injective
  rw [map_smul, primitiveCoordinate_anticanonical, smul_eq_mul, mul_one]

/-- The chosen normalization is forced once the primitive positive class is sent to three. -/
theorem normalizedCoordinate_unique (f : ComplexifiedClass →ₗ[ℂ] ℂ)
    (hf : f ((1 : ℂ) ⊗ₜ[ℤ] anticanonicalClass) = 3) :
    f = normalizedCoordinate.toLinearMap := by
  apply LinearMap.ext
  intro x
  change f x = normalizedCoordinate x
  conv_lhs => rw [eq_smul_anticanonical x]
  rw [map_smul, hf, normalizedCoordinate_apply]
  exact mul_comm _ _

/-- Scalar extension into the original complex character-divisor quotient. -/
def scalarExtension : ComplexifiedClass ≃ₗ[ℂ] Class ℂ :=
  normalizedCoordinate.trans (classParameter ℂ).symm

@[simp]
theorem scalarExtension_parameter (x : ComplexifiedClass) :
    classParameter ℂ (scalarExtension x) = normalizedCoordinate x :=
  (classParameter ℂ).apply_symm_apply _

/-- The comparison extends the class of every integral support divisor. -/
theorem scalarExtension_integral (c : ℂ) (d : cartierDivisors) :
    scalarExtension (c ⊗ₜ[ℤ] integralClassOf d) =
      c • classOf ℂ ((d.val.1 : ℂ), (d.val.2 : ℂ)) := by
  apply (classParameter ℂ).injective
  rw [scalarExtension_parameter, normalizedCoordinate_integral, map_smul,
    classParameter_classOf]
  rfl

/-- A general complex divisor gives a class in the complexified integral lattice. -/
def ofDivisor : (ℂ × ℂ) →ₗ[ℂ] ComplexifiedClass :=
  scalarExtension.symm.toLinearMap.comp (classOf ℂ)

@[simp]
theorem normalizedCoordinate_ofDivisor (d : ℂ × ℂ) :
    normalizedCoordinate (ofDivisor d) = d.1 + 2 * d.2 := by
  rw [← scalarExtension_parameter]
  change classParameter ℂ (scalarExtension (scalarExtension.symm (classOf ℂ d))) = _
  rw [scalarExtension.apply_symm_apply, classParameter_classOf]

theorem ofDivisor_integral (d : cartierDivisors) :
    ofDivisor ((d.val.1 : ℂ), (d.val.2 : ℂ)) =
      (1 : ℂ) ⊗ₜ[ℤ] integralClassOf d := by
  apply scalarExtension.injective
  change scalarExtension (scalarExtension.symm (classOf ℂ _)) = _
  rw [scalarExtension.apply_symm_apply, scalarExtension_integral, one_smul]

end Cubic.ToricHeights.ComplexifiedCartierClasses
