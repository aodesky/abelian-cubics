import Cubic.QuadraticCorrespondence.QuotientLocalCharacters
import Cubic.ToricHeights.InertLocalHeight

/-!
# Character-defined logarithms at the inert local places

For every point of the descended quotient over `ℚ_[p]`, evaluate its
invariant-ring characters in the constructed inert extension. The cocharacter
determined by these evaluations agrees with the valuation used in the local
Fourier integral. In particular both conjugate characters have the same
integer valuation: no factor two or one-half belongs in the cocharacter.

This is an algebraic local comparison. The topology on original quotient
points is compared in `QuotientLocalModels`, the integral locus in
`QuotientLocalIntegrality`, and the adelic assembly is in
`Cubic.PoissonSummation.FiniteAdelicData`.
-/

noncomputable section

namespace Cubic.ToricHeights.InertQuotientLogarithm

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois CyclotomicRestrictionScalars QuotientLocalCharacters
open CyclotomicInertField (Extension)
open Cubic.OrbitParametrization.CocharacterLattice

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

/-- The local place of the tensor algebra, with the global root sent to the
distinguished local root. Its construction precedes the height formula. -/
def place : E ⊗[ℚ] ℚ_[p] ≃ₐ[ℚ] Extension p :=
  (CyclotomicBaseChange.paperPresentation ℚ_[p]).trans
    ((CyclotomicInertField.quotientEquiv p).symm.restrictScalars ℚ)

@[simp]
theorem place_zeta : place p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p])) =
    CyclotomicInertField.zeta p := by
  simp only [place, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    CyclotomicBaseChange.paperPresentation_zeta]
  rfl

@[simp]
theorem place_scalar (a : ℚ_[p]) : place p ((1 : E) ⊗ₜ[ℚ] a) =
    algebraMap ℚ_[p] (Extension p) a := by
  simp [place, CyclotomicBaseChange.paperPresentation,
    CyclotomicBaseChange.presentation, CyclotomicInertField.quotientEquiv]
  rfl

/-- The local norm-preserving automorphism is the base change of global conjugation. -/
theorem place_conjugation (x : E ⊗[ℚ] ℚ_[p]) :
    place p (baseChangeConjugation ℚ_[p] x) =
      CyclotomicInertField.conjugation p (place p x) := by
  apply map_baseChangeConjugation ℚ_[p] (place p).toAlgHom
    ((CyclotomicInertField.conjugation p).restrictScalars ℚ)
  · simp
  · intro a
    simp

/-- The quotient point's local cyclotomic coordinate. No lift to the cover is needed. -/
def localPoint (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : InertLocalModel.Points p :=
  Units.map (place p).toMonoidHom (quotientRestrictionScalarsEquiv ℚ_[p] P)

theorem mapped_conjugate (u : (E ⊗[ℚ] ℚ_[p])ˣ) :
    Units.map (place p).toMonoidHom (conjugateUnit ℚ_[p] u) =
      Units.map (CyclotomicInertField.conjugation p).toMonoidHom
        (Units.map (place p).toMonoidHom u) := by
  apply Units.ext
  exact place_conjugation p u

theorem ord_conjugate (x : InertLocalModel.Points p) :
    InertLocalModel.ord p (Units.map (CyclotomicInertField.conjugation p).toMonoidHom x) =
      InertLocalModel.ord p x := by
  apply InertLocalModel.ord_eq_of_norm_eq
  change ‖CyclotomicInertField.conjugation p (x : Extension p)‖ = _
  rw [CyclotomicInertField.norm_conjugation, InertLocalModel.norm_eq_zpow_ord]

/-- Both basis-character valuations coincide, including for negative valuations. -/
theorem basisValuations_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    basisValuations ℚ_[p] (place p).toRingHom (InertLocalModel.integerValuation p) P =
      (InertLocalModel.ord p (localPoint p P), InertLocalModel.ord p (localPoint p P)) := by
  apply Prod.ext
  · rfl
  · change InertLocalModel.ord p
      (Units.map (place p).toMonoidHom
        (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P))) = _
    rw [mapped_conjugate, ord_conjugate]
    rfl

/-- The original character-defined cocharacter equals the one used in the inert Fourier model. -/
theorem localCocharacter_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localCocharacter ℚ_[p] (place p).toRingHom (InertLocalModel.integerValuation p) P =
      (InertLocalModel.valuation p (localPoint p P)).toAdd.val := by
  rw [localCocharacter, basisValuations_eq]
  ext <;> simp [CocharacterIsomorphism.fromCyclotomic, InertLocalModel.valuation,
    InertLocalModel.integerValuation, invariantCoordinate]
  ring

/-- The valuation of every original quotient character is paired with the model's lattice vector. -/
theorem character_pairing (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (m : ℤ × ℤ) :
    ((CharacterLattice.pullback m).1 : ℚ) *
        (coordinates (InertLocalModel.valuation p (localPoint p P)).toAdd).1 +
      ((CharacterLattice.pullback m).2 : ℚ) *
        (coordinates (InertLocalModel.valuation p (localPoint p P)).toAdd).2 =
      (InertLocalModel.ord p
        (localCharacter ℚ_[p] (place p).toRingHom P (Multiplicative.ofAdd m)) : ℚ) := by
  have h := localCocharacter_pairing ℚ_[p] (place p).toRingHom
    (InertLocalModel.integerValuation p) P m
  dsimp only at h
  rw [localCocharacter_eq] at h
  exact h

/-- The model's height coordinates are the original character-defined logarithm;
the inert ramification index is one. -/
theorem rayCoordinates_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    let n := coordinates
      (localCocharacter ℚ_[p] (place p).toRingHom (InertLocalModel.integerValuation p) P)
    InertLocalModel.rayCoordinates p (localPoint p P) = ((n.1 : ℝ), (n.2 : ℝ)) := by
  dsimp only
  rw [localCocharacter_eq]
  rfl

/-- The inverse height's support-function argument comes from the quotient characters. -/
theorem inverseHeight_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (s₀ σ : ℂ) :
    let n := coordinates
      (localCocharacter ℚ_[p] (place p).toRingHom (InertLocalModel.integerValuation p) P)
    InertLocalModel.inverseHeight p s₀ σ (localPoint p P) =
      (p : ℂ) ^ supportFunction s₀ σ ((n.1 : ℝ), (n.2 : ℝ)) := by
  dsimp only
  rw [InertLocalModel.inverseHeight, rayCoordinates_eq]

/-- The spectral character has the negative sign and both character valuations.
Inverting it in the Fourier integral therefore produces `σ-πit`. -/
theorem character_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (t : ℝ) :
    let n := coordinates
      (localCocharacter ℚ_[p] (place p).toRingHom (InertLocalModel.integerValuation p) P)
    InertLocalModel.character p t (localPoint p P) =
      Circle.exp (-Real.pi * t * Real.log p * ((n.1 : ℝ) + (n.2 : ℝ))) := by
  dsimp only
  have h := InertLocalModel.rayCoordinates_sum p (localPoint p P)
  rw [rayCoordinates_eq] at h
  change Circle.exp (-Real.pi * t * Real.log p *
    (InertLocalModel.degree p (localPoint p P) : ℝ)) = _
  rw [← h]

end Cubic.ToricHeights.InertQuotientLogarithm
