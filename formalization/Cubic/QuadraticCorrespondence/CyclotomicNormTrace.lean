import Cubic.QuadraticCorrespondence.CyclotomicConjugation
import Cubic.QuadraticCorrespondence.CyclotomicCoefficients
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Positivity

/-!
# The norm and trace of the global quadratic field

Relate mathlib's field norm and trace to the two Galois automorphisms
and to the cyclotomic coordinate formulas. These identities justify using the
explicit forms in the paper's coefficient and height calculations.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicField

open scoped Classical
open CyclotomicCoefficients

private theorem automorphisms_univ :
    (Finset.univ : Finset (E ≃ₐ[ℚ] E)) = {AlgEquiv.refl, conjugation} := by
  classical
  ext τ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact automorphism_eq_identity_or_conjugation τ

theorem norm_eq_mul_conjugation (x : E) :
    algebraMap ℚ E (Algebra.norm ℚ x) = x * conjugation x := by
  classical
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  rw [Algebra.norm_eq_prod_automorphisms, automorphisms_univ]
  simp [Ne.symm conjugation_ne_identity]

theorem trace_eq_add_conjugation (x : E) :
    algebraMap ℚ E (Algebra.trace ℚ E x) = x + conjugation x := by
  classical
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  rw [trace_eq_sum_automorphisms, automorphisms_univ]
  simp [Ne.symm conjugation_ne_identity]

theorem norm_linear (u v : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ E u + algebraMap ℚ E v * zeta) = normForm u v := by
  apply (algebraMap ℚ E).injective
  rw [norm_eq_mul_conjugation]
  simp only [map_add, map_mul, conjugation.commutes, conjugation_zeta]
  rw [linear_mul_conjugate zeta _ _ zeta_relation]
  simp only [normForm, map_sub, map_add, map_pow, map_mul]

theorem trace_linear (u v : ℚ) :
    Algebra.trace ℚ E (algebraMap ℚ E u + algebraMap ℚ E v * zeta) = traceForm u v := by
  apply (algebraMap ℚ E).injective
  rw [trace_eq_add_conjugation]
  simp only [map_add, map_mul, conjugation.commutes, conjugation_zeta]
  rw [linear_add_conjugate]
  simp only [traceForm, map_sub, map_mul, map_ofNat]

/-- The field norm is strictly positive on every nonzero element of this imaginary quadratic field. -/
theorem norm_pos {x : E} (hx : x ≠ 0) : 0 < Algebra.norm ℚ x := by
  obtain ⟨u, v, rfl⟩ := exists_linear x
  rw [norm_linear]
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hx
  unfold normForm
  rcases huv with hu | hv
  · nlinarith [sq_pos_of_ne_zero hu, sq_nonneg v, sq_nonneg (u - v)]
  · nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u, sq_nonneg (u - v)]

theorem quadratic_norm_trace (x : E) :
    x ^ 2 - algebraMap ℚ E (Algebra.trace ℚ E x) * x +
      algebraMap ℚ E (Algebra.norm ℚ x) = 0 := by
  rw [trace_eq_add_conjugation, norm_eq_mul_conjugation]
  ring

end Cubic.QuadraticCorrespondence.CyclotomicField
