import Cubic.QuadraticCorrespondence.CyclotomicTorusDescent
import Mathlib.RingTheory.Flat.Basic

/-!
# Descent of coefficients from the cyclotomic scalar extension

For every commutative rational algebra `A`, the elements fixed by conjugation
in `E ⊗[ℚ] A` are exactly the image of `A`. This supplies coefficient descent
for points of the cover and quotient, including over nonreduced algebras.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicScalarDescent

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois

variable (A : Type*) [CommRing A] [Algebra ℚ A]

theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap ℚ E).injective

@[simp]
theorem conjugation_tmul (c : E) (a : A) :
    baseChangeConjugation A (c ⊗ₜ[ℚ] a) = conjugation c ⊗ₜ[ℚ] a := rfl

@[simp]
theorem conjugation_one_tmul (a : A) :
    baseChangeConjugation A ((1 : E) ⊗ₜ[ℚ] a) = (1 : E) ⊗ₜ[ℚ] a := by
  simp [baseChangeConjugation]

theorem fixed_iff (x : E ⊗[ℚ] A) :
    baseChangeConjugation A x = x ↔ ∃ a : A, (1 : E) ⊗ₜ[ℚ] a = x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ :=
      QuadraticDescent.exists_tensor_decomposition sqrtNegThree exists_sqrtNegThree_linear x
    have hδb : sqrtNegThree ⊗ₜ[ℚ] b = -(sqrtNegThree ⊗ₜ[ℚ] b) := by
      simpa only [map_add, conjugation_one_tmul, conjugation_tmul,
        map_one, conjugation_sqrtNegThree, TensorProduct.neg_tmul, add_right_inj] using hx.symm
    have hz : (2 * sqrtNegThree) • ((1 : E) ⊗ₜ[ℚ] b) = 0 := by
      calc
        (2 * sqrtNegThree) • ((1 : E) ⊗ₜ[ℚ] b) =
            sqrtNegThree ⊗ₜ[ℚ] b + sqrtNegThree ⊗ₜ[ℚ] b := by
          simp [TensorProduct.smul_tmul', smul_eq_mul, two_mul, TensorProduct.add_tmul]
        _ = 0 := by nth_rw 1 [hδb]; exact neg_add_cancel _
    have hb : (1 : E) ⊗ₜ[ℚ] b = 0 :=
      (smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) sqrtNegThree_ne_zero)
    have hb0 : b = 0 := includeRight_injective A (by simpa using hb)
    exact ⟨a, by simp [hb0]⟩
  · rintro ⟨a, rfl⟩
    exact conjugation_one_tmul A a

/-- The coefficient algebra maps into the fixed subalgebra. -/
def includeFixed : A →ₐ[ℚ] QuadraticDescent.fixedRing (baseChangeConjugation A) :=
  (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A).codRestrict _
    (fun a => conjugation_one_tmul A a)

theorem includeFixed_bijective : Function.Bijective (includeFixed A) := by
  constructor
  · intro a b h
    exact includeRight_injective A (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := (fixed_iff A x).mp x.property
    exact ⟨a, Subtype.ext ha⟩

/-- Effective coefficient descent, with the standard inclusion as its forward map. -/
def fixedEquiv : A ≃ₐ[ℚ] QuadraticDescent.fixedRing (baseChangeConjugation A) :=
  AlgEquiv.ofBijective (includeFixed A) (includeFixed_bijective A)

@[simp]
theorem fixedEquiv_apply (a : A) :
    (fixedEquiv A a : E ⊗[ℚ] A) = (1 : E) ⊗ₜ[ℚ] a := rfl

end Cubic.QuadraticCorrespondence.CyclotomicScalarDescent
