import Cubic.QuadraticCorrespondence.CyclotomicField

/-!
# Conjugation on the global cyclotomic field

Construct the nontrivial automorphism of `E = ℚ(ζ₃)` by the universal property
of its power basis. Its square is the identity and its fixed elements are
exactly the rational scalars. This supplies the coefficient automorphism for
the semilinear Laurent-ring comparison.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicField

open Polynomial

private def conjugationHom : E →ₐ[ℚ] E :=
  (zeta_primitive.powerBasis ℚ).lift (-1 - zeta) (by
    simp only [IsPrimitiveRoot.powerBasis_gen, minpoly_zeta, cyclotomic_three,
      map_add, map_pow, aeval_X, map_one]
    exact CyclotomicLocalAlgebra.other_root zeta zeta_relation)

private theorem conjugationHom_zeta : conjugationHom zeta = -1 - zeta := by
  exact (zeta_primitive.powerBasis ℚ).lift_gen _ _

private theorem conjugationHom_comp : conjugationHom.comp conjugationHom = AlgHom.id ℚ E := by
  apply (zeta_primitive.powerBasis ℚ).algHom_ext
  change conjugationHom (conjugationHom zeta) = zeta
  simp only [conjugationHom_zeta, map_sub, map_neg, map_one]
  ring

/-- The nontrivial rational automorphism of the cyclotomic field. -/
def conjugation : E ≃ₐ[ℚ] E :=
  AlgEquiv.ofAlgHom conjugationHom conjugationHom conjugationHom_comp conjugationHom_comp

theorem conjugation_zeta : conjugation zeta = -1 - zeta := conjugationHom_zeta

theorem conjugation_zeta_sq : conjugation zeta = zeta ^ 2 := by
  rw [conjugation_zeta]
  linear_combination -zeta_relation

theorem conjugation_involutive : Function.Involutive conjugation := by
  intro x
  exact DFunLike.congr_fun conjugationHom_comp x

theorem conjugation_ne_identity : conjugation ≠ AlgEquiv.refl := by
  intro h
  have hz : zeta = -1 - zeta := by simpa [h] using conjugation_zeta
  exact CyclotomicLocalAlgebra.roots_distinct zeta zeta_relation hz

/-- These are all the automorphisms, so the involution generates the
Galois action used in the paper. -/
theorem automorphism_eq_identity_or_conjugation (τ : E ≃ₐ[ℚ] E) :
    τ = AlgEquiv.refl ∨ τ = conjugation := by
  have hroot : (τ zeta) ^ 2 + τ zeta + 1 = 0 := by
    simpa using congrArg τ zeta_relation
  have hprod : (τ zeta - zeta) * (τ zeta + zeta + 1) = 0 := by
    linear_combination hroot - zeta_relation
  rcases mul_eq_zero.mp hprod with h | h
  · left
    have hhom : τ.toAlgHom = AlgHom.id ℚ E :=
      (zeta_primitive.powerBasis ℚ).algHom_ext (sub_eq_zero.mp h)
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hhom x
  · right
    have hz : τ zeta = conjugation zeta := by
      rw [conjugation_zeta]
      linear_combination h
    have hhom : τ.toAlgHom = conjugation.toAlgHom :=
      (zeta_primitive.powerBasis ℚ).algHom_ext hz
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hhom x

/-- Every element of the global field is determined by its cyclotomic coordinates. -/
theorem exists_linear (x : E) :
    ∃ a b : ℚ, x = algebraMap ℚ E a + algebraMap ℚ E b * zeta := by
  let pb := zeta_primitive.powerBasis ℚ
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hd : f.natDegree < 2 := by
    simpa only [pb, IsPrimitiveRoot.powerBasis_dim, minpoly_zeta,
      natDegree_cyclotomic] using hdeg
  have he := f.eq_X_add_C_of_degree_le_one
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hf, he]
  simp [pb, IsPrimitiveRoot.powerBasis_gen, add_comm]

theorem sqrtNegThree_ne_zero : sqrtNegThree ≠ 0 := by
  intro hz
  have hs := sqrtNegThree_sq
  rw [hz] at hs
  norm_num at hs

theorem conjugation_sqrtNegThree : conjugation sqrtNegThree = -sqrtNegThree := by
  simp only [sqrtNegThree, map_add, map_mul, map_ofNat, conjugation_zeta, map_one]
  ring

/-- The anti-invariant generator gives the quadratic basis used for descent. -/
theorem exists_sqrtNegThree_linear (x : E) :
    ∃ a b : ℚ, x = a • (1 : E) + b • sqrtNegThree := by
  obtain ⟨a, b, hx⟩ := exists_linear x
  refine ⟨a - b / 2, b / 2, ?_⟩
  rw [hx]
  simp [Algebra.smul_def, map_sub, map_div₀, sqrtNegThree]
  ring

/-- The fixed field of this involution is precisely the rational ground field. -/
theorem conjugation_fixed_iff (x : E) :
    conjugation x = x ↔ ∃ a : ℚ, algebraMap ℚ E a = x := by
  constructor
  · intro h
    obtain ⟨a, b, hx⟩ := exists_linear x
    have hb : algebraMap ℚ E b * sqrtNegThree = 0 := by
      rw [hx, map_add, map_mul, conjugation.commutes, conjugation.commutes,
        conjugation_zeta] at h
      dsimp [sqrtNegThree]
      linear_combination -h
    have hb0 := (mul_eq_zero.mp hb).resolve_right sqrtNegThree_ne_zero
    exact ⟨a, by rw [hx, hb0, zero_mul, add_zero]⟩
  · rintro ⟨a, rfl⟩
    exact conjugation.commutes a

end Cubic.QuadraticCorrespondence.CyclotomicField
