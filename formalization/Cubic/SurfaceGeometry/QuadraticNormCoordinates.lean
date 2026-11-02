import Cubic.SurfaceGeometry.RationalFormData
import Cubic.QuadraticCorrespondence.CyclotomicScalarDescent

noncomputable section

namespace Cubic.SurfaceGeometry.QuadraticNormCoordinates

open RationalFormData Cubic.QuadraticCorrespondence
open CyclotomicField CyclotomicTorusGalois CyclotomicScalarDescent
open scoped TensorProduct

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem element_eq_zero_iff (a b : R) : quadraticElement a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hx : baseChangeConjugation R (quadraticElement a b) = quadraticElement a b := by
      rw [h, map_zero]
    have hb' : sqrtNegThree ⊗ₜ[ℚ] b = -(sqrtNegThree ⊗ₜ[ℚ] b) := by
      simpa only [quadraticElement, map_add, conjugation_one_tmul, conjugation_tmul,
        map_one, conjugation_sqrtNegThree, TensorProduct.neg_tmul, add_right_inj] using hx.symm
    have hz : (2 * sqrtNegThree) • ((1 : E) ⊗ₜ[ℚ] b) = 0 := by
      calc
        _ = sqrtNegThree ⊗ₜ[ℚ] b + sqrtNegThree ⊗ₜ[ℚ] b := by
          simp [TensorProduct.smul_tmul', smul_eq_mul, two_mul, TensorProduct.add_tmul]
        _ = 0 := by nth_rw 1 [hb']; exact neg_add_cancel _
    have hb : b = 0 := includeRight_injective R (by
      simpa using (smul_eq_zero.mp hz).resolve_left
        (mul_ne_zero (by norm_num) sqrtNegThree_ne_zero))
    refine ⟨includeRight_injective R ?_, hb⟩
    simpa [quadraticElement,hb] using h
  · rintro ⟨rfl,rfl⟩
    simp [quadraticElement]

theorem element_injective : Function.Injective
    (fun p : R × R => quadraticElement p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hz : quadraticElement (a-c) (b-d) = 0 := by
    calc
      _ = quadraticElement a b - quadraticElement c d := by
        simp [quadraticElement,TensorProduct.tmul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr h
  obtain ⟨ha,hb⟩ := (element_eq_zero_iff _ _).mp hz
  exact Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

theorem element_surjective : Function.Surjective
    (fun p : R × R => quadraticElement p.1 p.2) := by
  intro x
  obtain ⟨a,b,h⟩ := QuadraticDescent.exists_tensor_decomposition sqrtNegThree
    exists_sqrtNegThree_linear x
  exact ⟨(a,b),h.symm⟩

theorem element_as_polynomial (a b : R) : quadraticElement a b =
    Algebra.TensorProduct.includeRight a +
      algebraMap E (E ⊗[ℚ] R) sqrtNegThree * Algebra.TensorProduct.includeRight b := by
  simp [quadraticElement,Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem element_mul (a b c d : R) :
    quadraticElement a b * quadraticElement c d =
      quadraticElement (a*c-3*b*d) (a*d+b*c) := by
  have hr : (algebraMap E (E ⊗[ℚ] R) sqrtNegThree) ^ 2 = -3 := by
    rw [← map_pow, sqrtNegThree_sq]
    simp only [map_neg, map_ofNat]
  simp only [element_as_polynomial, map_add, map_sub, map_mul, map_ofNat]
  linear_combination
    (Algebra.TensorProduct.includeRight b * Algebra.TensorProduct.includeRight d) * hr

@[simp] theorem element_one : quadraticElement (1 : R) 0 = 1 := by
  simp [quadraticElement,Algebra.TensorProduct.one_def]

theorem element_norm (a b : R) :
    quadraticElement a b * quadraticElement a (-b) =
      quadraticElement (a^2+3*b^2) 0 := by
  rw [element_mul]
  congr 1 <;> ring

theorem norm_mul (a b c d : R) :
    (a*c-3*b*d)^2+3*(a*d+b*c)^2 = (a^2+3*b^2)*(c^2+3*d^2) := by ring

theorem element_map {S : Type*} [CommRing S] [Algebra ℚ S]
    (φ : R →ₐ[ℚ] S) (a b : R) :
    Algebra.TensorProduct.map (AlgHom.id E E) φ (quadraticElement a b) =
      quadraticElement (φ a) (φ b) := by
  simp [quadraticElement]

end Cubic.SurfaceGeometry.QuadraticNormCoordinates
