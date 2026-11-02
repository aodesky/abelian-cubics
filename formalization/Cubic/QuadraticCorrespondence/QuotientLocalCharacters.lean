import Cubic.QuadraticCorrespondence.RationalQuotientGroup
import Cubic.QuadraticCorrespondence.CharacterLattice

/-!
# Quotient characters and the local valuation pairing

The characters are units of the cyclic invariant ring: in cover
coordinates their exponents are `(2a-b, -a+2b)`. Evaluate them by scalar
extension of a point of the descended quotient, with no cover lift assumed.
Their valuations determine the paper's enlarged cocharacter lattice uniquely.

The place map and its integer valuation are explicit arguments here; the
local height modules instantiate them at each place.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientLocalCharacters

open scoped TensorProduct RationalQuotientGroup
open CyclotomicField CyclotomicTorusGalois CyclotomicPointDescent
open CyclotomicRestrictionScalars RationalQuotientGroup
open SplitLaurentInvariants SplitLaurentPoints SplitLaurentEvaluation SplitCoverFunctor
open Cubic.OrbitParametrization.CyclicGroupAlgebra

/-- A character of the split quotient, as a unit of its invariant coordinate ring. -/
def quotientCharacter : Multiplicative (ℤ × ℤ) →*
    (invariantRing (rootUnit zeta zeta_relation))ˣ :=
  (Units.map (invariantEquiv (rootUnit zeta zeta_relation)
    (rootUnit_primitive zeta zeta_relation)).toMonoidHom).comp monomialUnit

/-- The character is the specified invariant monomial in the cover ring. -/
theorem quotientCharacter_coe (m : ℤ × ℤ) :
    (((quotientCharacter (Multiplicative.ofAdd m) :
      (invariantRing (rootUnit zeta zeta_relation))ˣ) :
      invariantRing (rootUnit zeta zeta_relation)) : LaurentRing (K := E)) =
        AddMonoidAlgebra.single (CharacterLattice.pullback m) 1 := by
  change pullbackHom (AddMonoidAlgebra.single m (1 : E)) = _
  exact pullbackHom_single m 1

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Evaluate invariant-ring characters on the scalar extension of a quotient point. -/
def characterValues (P : quotientFixedRing →ₐ[ℚ] A) :
    Multiplicative (ℤ × ℤ) →* (E ⊗[ℚ] A)ˣ :=
  (Units.map (extendQuotient A P).toMonoidHom).comp quotientCharacter

theorem characterValues_eq (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    characterValues A P (Multiplicative.ofAdd m) =
      Units.map (extendPoint (quotientPresentation A P)).toMonoidHom
        (monomialUnit (Multiplicative.ofAdd m)) := by
  apply Units.ext
  change extendPoint (quotientPresentation A P)
    ((invariantEquiv (rootUnit zeta zeta_relation)
      (rootUnit_primitive zeta zeta_relation)).symm
        ((invariantEquiv (rootUnit zeta zeta_relation)
          (rootUnit_primitive zeta zeta_relation)) _)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

theorem extended_coordinates (P : quotientFixedRing →ₐ[ℚ] A) :
    coordinates (extendPoint (quotientPresentation A P)) =
      (quotientRestrictionScalarsEquiv A P,
        conjugateUnit A (quotientRestrictionScalarsEquiv A P)) := by
  apply Prod.ext
  · rfl
  · apply Units.ext
    have h := extendPoint_conjugate (quotientPresentation A P)
      (AddMonoidAlgebra.single (1, 0) (1 : E))
    simpa only [SplitLaurentGalois.conjugate_single, map_one, Prod.swap_prod_mk] using h

/-- Evaluation in the quotient's own character basis, for every integer exponent. -/
theorem characterValues_formula (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    characterValues A P (Multiplicative.ofAdd m) =
      quotientRestrictionScalarsEquiv A P ^ m.1 *
        conjugateUnit A (quotientRestrictionScalarsEquiv A P) ^ m.2 := by
  rw [characterValues_eq, ← pointCharacter_coordinates, extended_coordinates]
  rfl

/-- These invariant functions are multiplicative for the descended quotient law. -/
theorem characterValues_mul (P Q : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    characterValues A (P * Q) (Multiplicative.ofAdd m) =
      characterValues A P (Multiplicative.ofAdd m) *
        characterValues A Q (Multiplicative.ofAdd m) := by
  simp only [characterValues_formula, ← quotientRestrictionScalarsMulEquiv_apply, map_mul,
    conjugateUnit]
  rw [mul_zpow (quotientRestrictionScalarsMulEquiv A P) (quotientRestrictionScalarsMulEquiv A Q),
    mul_zpow (Units.map (baseChangeConjugation A).toMonoidHom (quotientRestrictionScalarsMulEquiv A P))
      (Units.map (baseChangeConjugation A).toMonoidHom (quotientRestrictionScalarsMulEquiv A Q))]
  exact mul_mul_mul_comm (quotientRestrictionScalarsMulEquiv A P ^ m.1)
    (quotientRestrictionScalarsMulEquiv A Q ^ m.1)
    (Units.map (baseChangeConjugation A).toMonoidHom (quotientRestrictionScalarsMulEquiv A P) ^ m.2)
    (Units.map (baseChangeConjugation A).toMonoidHom (quotientRestrictionScalarsMulEquiv A Q) ^ m.2)

/-- A local conjugation agrees with the global one if it fixes base scalars
and sends the distinguished root to its conjugate. -/
theorem map_baseChangeConjugation {L : Type*} [CommRing L] [Algebra ℚ L]
    (place : E ⊗[ℚ] A →ₐ[ℚ] L) (τ : L ≃ₐ[ℚ] L)
    (hζ : τ (place (zeta ⊗ₜ[ℚ] (1 : A))) = -1 - place (zeta ⊗ₜ[ℚ] (1 : A)))
    (hA : ∀ a : A, τ (place ((1 : E) ⊗ₜ[ℚ] a)) = place ((1 : E) ⊗ₜ[ℚ] a))
    (x : E ⊗[ℚ] A) :
    place (baseChangeConjugation A x) = τ (place x) := by
  have he : place.comp (baseChangeConjugation A).toAlgHom = τ.toAlgHom.comp place := by
    apply Algebra.TensorProduct.ext
    · apply (zeta_primitive.powerBasis ℚ).algHom_ext
      change place (baseChangeConjugation A (zeta ⊗ₜ[ℚ] (1 : A))) =
        τ (place (zeta ⊗ₜ[ℚ] (1 : A)))
      rw [hζ]
      simp [baseChangeConjugation, conjugation_zeta, TensorProduct.sub_tmul,
        TensorProduct.neg_tmul]
      exact place.map_one
    · apply AlgHom.ext
      intro a
      change place (baseChangeConjugation A ((1 : E) ⊗ₜ[ℚ] a)) =
        τ (place ((1 : E) ⊗ₜ[ℚ] a))
      simpa [baseChangeConjugation] using (hA a).symm
  exact DFunLike.congr_fun he x

variable {L : Type*} [CommRing L]
variable (place : E ⊗[ℚ] A →+* L) (ord : Lˣ →* Multiplicative ℤ)

/-- Character evaluation after the chosen local place map. -/
def localCharacter (P : quotientFixedRing →ₐ[ℚ] A) :
    Multiplicative (ℤ × ℤ) →* Lˣ :=
  (Units.map place.toMonoidHom).comp (characterValues A P)

/-- The two integer character valuations, before any ramification normalization. -/
def basisValuations (P : quotientFixedRing →ₐ[ℚ] A) : ℤ × ℤ :=
  ((ord (Units.map place.toMonoidHom (quotientRestrictionScalarsEquiv A P))).toAdd,
    (ord (Units.map place.toMonoidHom
      (conjugateUnit A (quotientRestrictionScalarsEquiv A P)))).toAdd)

/-- Taking the valuation of a character is the integral pairing with its exponent. -/
theorem localCharacter_valuation (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    (ord (localCharacter A place P (Multiplicative.ofAdd m))).toAdd =
      m.1 * (basisValuations A place ord P).1 +
        m.2 * (basisValuations A place ord P).2 := by
  simp [localCharacter, characterValues_formula, basisValuations]

/-- The cocharacter determined by character valuations, in the paper's integral basis. -/
def localCocharacter (P : quotientFixedRing →ₐ[ℚ] A) : ℤ × ℤ :=
  CocharacterIsomorphism.fromCyclotomic (basisValuations A place ord P)

/-- The character-defined logarithm turns the original quotient product into lattice addition. -/
theorem localCocharacter_mul (P Q : quotientFixedRing →ₐ[ℚ] A) :
    localCocharacter A place ord (P * Q) =
      localCocharacter A place ord P + localCocharacter A place ord Q := by
  unfold localCocharacter
  rw [← map_add]
  congr 1
  ext <;> simp [basisValuations, ← quotientRestrictionScalarsMulEquiv_apply, conjugateUnit]

/-- This is the defining local-logarithm pairing in the enlarged lattice.
The cover exponents and the thirds in the ray coordinates cancel by duality. -/
theorem localCocharacter_pairing (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    let n := Cubic.OrbitParametrization.CocharacterLattice.coordinates
      (localCocharacter A place ord P)
    ((CharacterLattice.pullback m).1 : ℚ) * n.1 +
      ((CharacterLattice.pullback m).2 : ℚ) * n.2 =
        ((ord (localCharacter A place P (Multiplicative.ofAdd m))).toAdd : ℚ) := by
  dsimp only [localCocharacter]
  rw [CharacterLattice.pairing_fromCyclotomic, localCharacter_valuation]
  push_cast
  rfl

/-- No other lattice vector has these character valuations. -/
theorem localCocharacter_unique (P : quotientFixedRing →ₐ[ℚ] A) (n : ℤ × ℤ)
    (hn : ∀ m : ℤ × ℤ,
      ((CharacterLattice.pullback m).1 : ℚ) *
          (Cubic.OrbitParametrization.CocharacterLattice.coordinates n).1 +
        ((CharacterLattice.pullback m).2 : ℚ) *
          (Cubic.OrbitParametrization.CocharacterLattice.coordinates n).2 =
        ((ord (localCharacter A place P (Multiplicative.ofAdd m))).toAdd : ℚ)) :
    n = localCocharacter A place ord P := by
  obtain ⟨k, rfl⟩ := CocharacterIsomorphism.fromCyclotomic.surjective n
  unfold localCocharacter
  congr 1
  have h₁ := hn (1, 0)
  have h₂ := hn (0, 1)
  rw [CharacterLattice.pairing_fromCyclotomic, localCharacter_valuation] at h₁ h₂
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at h₁ h₂
  exact Prod.ext (Int.cast_injective h₁) (Int.cast_injective h₂)

end Cubic.QuadraticCorrespondence.QuotientLocalCharacters
