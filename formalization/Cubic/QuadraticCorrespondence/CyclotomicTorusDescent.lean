import Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
import Cubic.QuadraticCorrespondence.QuadraticDescent

/-!
# Scalar extension of the rational cover and quotient rings

The fixed rings constructed from the cyclotomic Galois action recover
the split cover and its cyclic invariant ring after extension from `ℚ` to `E`.
Both comparisons are the natural multiplication maps on pure tensors. Thus
the fixed rings give effective descent of these coordinate algebras, not just
abstract algebras with a compatible action. `RationalCoverFunctor` and
`RationalQuotientFunctor` identify them with the original rational point functors.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicTorusDescent

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois SplitLaurentInvariants SplitCoverFunctor

/-- The natural scalar-extension map recovers the entire split cover ring. -/
def coverBaseChangeEquiv : E ⊗[ℚ] coverFixedRing ≃ₐ[E] LaurentRing (K := E) :=
  QuadraticDescent.baseChangeEquiv conjugation (SplitLaurentGalois.conjugate conjugation)
    (SplitLaurentGalois.conjugate_algebraMap conjugation)
    sqrtNegThree sqrtNegThree_ne_zero conjugation_sqrtNegThree (by norm_num)
    (SplitLaurentGalois.conjugate_involutive conjugation conjugation_involutive)
    exists_sqrtNegThree_linear

@[simp]
theorem coverBaseChangeEquiv_tmul (c : E) (f : coverFixedRing) :
    coverBaseChangeEquiv (c ⊗ₜ[ℚ] f) = c • (f : LaurentRing (K := E)) :=
  QuadraticDescent.baseChangeEquiv_tmul _ _ _ _ _ _ _ _ _ c f

/-- Scalar extension also recovers the full cyclic invariant coordinate ring. -/
def quotientBaseChangeEquiv :
    E ⊗[ℚ] quotientFixedRing ≃ₐ[E] invariantRing (rootUnit zeta zeta_relation) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) fixedRingEquiv.symm).trans
    coverBaseChangeEquiv).trans
      (invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation))

/-- The quotient comparison is the natural map on tensors, so it agrees with
the inclusion of invariant functions in the cover coordinate ring. -/
@[simp]
theorem quotientBaseChangeEquiv_tmul (c : E) (f : quotientFixedRing) :
    (quotientBaseChangeEquiv (c ⊗ₜ[ℚ] f) : LaurentRing (K := E)) =
      c • (f : LaurentRing (K := E)) := by
  change ((invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation))
    (coverBaseChangeEquiv (c ⊗ₜ[ℚ] fixedRingEquiv.symm f)) : LaurentRing (K := E)) = _
  rw [coverBaseChangeEquiv_tmul, map_smul]
  change c • pullbackHom (fixedRingEquiv.symm f : LaurentRing (K := E)) =
    c • (f : LaurentRing (K := E))
  exact congrArg (fun g : quotientFixedRing => c • (g : LaurentRing (K := E)))
    (fixedRingEquiv.apply_symm_apply f)

/-- The fixed-ring isomorphism extends to the split invariant-ring parametrization,
using exactly the quotient-character pullback. -/
theorem baseChange_quotient_compatibility (x : E ⊗[ℚ] coverFixedRing) :
    quotientBaseChangeEquiv
        (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) fixedRingEquiv x) =
      invariantEquiv (rootUnit zeta zeta_relation) (rootUnit_primitive zeta zeta_relation)
        (coverBaseChangeEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c f =>
    apply Subtype.ext
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      quotientBaseChangeEquiv_tmul, coverBaseChangeEquiv_tmul, map_smul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Cubic.QuadraticCorrespondence.CyclotomicTorusDescent
