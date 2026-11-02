import Cubic.QuadraticCorrespondence.CyclotomicPointDescent

/-!
# The descended Laurent ring represents restriction of scalars

For every commutative rational algebra `A`, its points are naturally identified
with the units of `E ⊗[ℚ] A`. In split coordinates an equivariant point is the
pair `(u, γu)`. Transport through the fixed-ring isomorphism gives the
same description for the descended cyclic quotient. These are natural
equivalences of point sets. `RationalCoverFunctor` proves the original rational
cover comparison, including its group structure. `RationalQuotientFunctor`
identifies restriction to invariant functions and its quotient-character formula.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRestrictionScalars

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicPointDescent
open SplitLaurentInvariants SplitLaurentEvaluation SplitLaurentPoints SplitLaurentGalois

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Conjugation on the unit group of the scalar extension. -/
def conjugateUnit (u : (E ⊗[ℚ] A)ˣ) : (E ⊗[ℚ] A)ˣ :=
  Units.map (baseChangeConjugation A).toMonoidHom u

theorem conjugateUnit_involutive : Function.Involutive (conjugateUnit A) := by
  intro u
  apply Units.ext
  exact baseChangeConjugation_involutive A (u : E ⊗[ℚ] A)

theorem evaluate_equivariant_iff (x : (E ⊗[ℚ] A)ˣ × (E ⊗[ℚ] A)ˣ) :
    IsEquivariant (evaluate (K := E) x) ↔ pointConjugate (baseChangeConjugation A) x = x := by
  constructor
  · intro hx
    have he : evaluate (K := E) (pointConjugate (baseChangeConjugation A) x) = evaluate x := by
      apply AlgHom.ext
      intro b
      obtain ⟨c, rfl⟩ := (conjugate conjugation).surjective b
      exact (evaluate_conjugate conjugation (baseChangeConjugation A)
        (baseChangeConjugation_algebraMap A) x c).trans (hx c).symm
    simpa only [coordinates_evaluate] using congrArg coordinates he
  · intro hx b
    have he := evaluate_conjugate conjugation (baseChangeConjugation A)
      (baseChangeConjugation_algebraMap A) x b
    rwa [hx] at he

/-- The second split coordinate is determined by the first through conjugation. -/
def fixedPairEquiv :
    {x : (E ⊗[ℚ] A)ˣ × (E ⊗[ℚ] A)ˣ // pointConjugate (baseChangeConjugation A) x = x} ≃
      (E ⊗[ℚ] A)ˣ where
  toFun x := x.val.1
  invFun u := ⟨(u, conjugateUnit A u), Prod.ext (conjugateUnit_involutive A u) rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change conjugateUnit A x.val.1 = x.val.2
      exact congrArg Prod.snd x.property
  right_inv _ := rfl

/-- Equivariance of a Laurent-ring point is precisely the fixed-pair condition. -/
def equivariantLaurentEquiv :
    {f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A // IsEquivariant f} ≃
      {x : (E ⊗[ℚ] A)ˣ × (E ⊗[ℚ] A)ˣ // pointConjugate (baseChangeConjugation A) x = x} :=
  pointEquiv.subtypeEquiv (fun f => by
    simpa only [evaluate_coordinates] using evaluate_equivariant_iff A (coordinates f))

/-- The rational fixed ring represents the unit functor of the quadratic scalar extension. -/
def restrictionScalarsEquiv : (coverFixedRing →ₐ[ℚ] A) ≃ (E ⊗[ℚ] A)ˣ :=
  equivariantPointEquiv.trans ((equivariantLaurentEquiv A).trans (fixedPairEquiv A))

/-- The descended cyclic quotient has the same restriction-of-scalars point functor. -/
def quotientRestrictionScalarsEquiv : (quotientFixedRing →ₐ[ℚ] A) ≃ (E ⊗[ℚ] A)ˣ :=
  (fixedRingEquiv.symm.arrowCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)).trans
    (restrictionScalarsEquiv A)

/-- The comparison commutes with every homomorphism of coefficient algebras. -/
theorem restrictionScalarsEquiv_comp {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (f : coverFixedRing →ₐ[ℚ] A) :
    restrictionScalarsEquiv A' (φ.comp f) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom
        (restrictionScalarsEquiv A f) := by
  change (coordinates (extendPoint (φ.comp f))).1 = _
  rw [extendPoint_comp, coordinates_comp]
  rfl

theorem quotientRestrictionScalarsEquiv_comp {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (f : quotientFixedRing →ₐ[ℚ] A) :
    quotientRestrictionScalarsEquiv A' (φ.comp f) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom
        (quotientRestrictionScalarsEquiv A f) :=
  restrictionScalarsEquiv_comp A φ (f.comp fixedRingEquiv.toAlgHom)

end Cubic.QuadraticCorrespondence.CyclotomicRestrictionScalars
