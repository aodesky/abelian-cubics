import Cubic.QuadraticCorrespondence.QuotientLocalCharacters
import Cubic.ToricHeights.RamifiedLocalValuation
import Cubic.ToricHeights.LocalDegreeNormalization

/-!
# Character-defined logarithms and the height denominator at three

Evaluate characters on arbitrary points of the descended quotient over `ℚ₃`.
The resulting integral cocharacter has ray coordinates `(ord_w, ord_w)`.
The norm-defined height coordinates are half this vector. Thus the division
by two occurs when forming the height, after the character-valuation pairing.

The comparison uses the global root, local conjugation and normalized
local valuation. It is a local statement; the adelic height is assembled in
`Cubic.PoissonSummation.FiniteAdelicData`.
-/

noncomputable section

namespace Cubic.ToricHeights.RamifiedQuotientLogarithm

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois CyclotomicRestrictionScalars QuotientLocalCharacters
open CyclotomicRamifiedField (Extension)
open Cubic.OrbitParametrization.CocharacterLattice

/-- The ramified place, specified on the distinguished cyclotomic root. -/
def place : E ⊗[ℚ] ℚ_[3] ≃ₐ[ℚ] Extension :=
  (CyclotomicBaseChange.paperPresentation ℚ_[3]).trans
    (CyclotomicRamifiedField.quotientEquiv.symm.restrictScalars ℚ)

@[simp]
theorem place_zeta : place (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[3])) =
    CyclotomicRamifiedField.zeta := by
  simp only [place, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    CyclotomicBaseChange.paperPresentation_zeta]
  rfl

@[simp]
theorem place_scalar (a : ℚ_[3]) : place ((1 : E) ⊗ₜ[ℚ] a) =
    algebraMap ℚ_[3] Extension a := by
  simp [place, CyclotomicBaseChange.paperPresentation,
    CyclotomicBaseChange.presentation, CyclotomicRamifiedField.quotientEquiv]
  rfl

theorem place_conjugation (x : E ⊗[ℚ] ℚ_[3]) :
    place (baseChangeConjugation ℚ_[3] x) =
      CyclotomicRamifiedField.conjugation (place x) := by
  apply map_baseChangeConjugation ℚ_[3] place.toAlgHom
    (CyclotomicRamifiedField.conjugation.restrictScalars ℚ)
  · simp
  · intro a
    simp

/-- The local parameter of a point of the original descended quotient. -/
def localPoint (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : RamifiedLocalModel.Points :=
  Units.map place.toMonoidHom (quotientRestrictionScalarsEquiv ℚ_[3] P)

theorem mapped_conjugate (u : (E ⊗[ℚ] ℚ_[3])ˣ) :
    Units.map place.toMonoidHom (conjugateUnit ℚ_[3] u) =
      Units.map CyclotomicRamifiedField.conjugation.toMonoidHom
        (Units.map place.toMonoidHom u) := by
  apply Units.ext
  exact place_conjugation u

theorem ord_conjugate (x : RamifiedLocalModel.Points) :
    RamifiedLocalModel.ord (Units.map CyclotomicRamifiedField.conjugation.toMonoidHom x) =
      RamifiedLocalModel.ord x := by
  have h : RamifiedLocalModel.logarithmicOrder
      (Units.map CyclotomicRamifiedField.conjugation.toMonoidHom x) =
      RamifiedLocalModel.logarithmicOrder x := by
    change -Real.log ‖CyclotomicRamifiedField.conjugation (x : Extension)‖ / Real.log 3 = _
    rw [CyclotomicRamifiedField.norm_conjugation]
    rfl
  simp only [RamifiedLocalModel.logarithmicOrder_eq_ord_div_two] at h
  exact_mod_cast (show
    (RamifiedLocalModel.ord (Units.map CyclotomicRamifiedField.conjugation.toMonoidHom x) : ℝ) =
      (RamifiedLocalModel.ord x : ℝ) by linarith)

theorem basisValuations_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    basisValuations ℚ_[3] place.toRingHom RamifiedLocalModel.integerValuation P =
      (RamifiedLocalModel.ord (localPoint P), RamifiedLocalModel.ord (localPoint P)) := by
  apply Prod.ext
  · rfl
  · change RamifiedLocalModel.ord
      (Units.map place.toMonoidHom
        (conjugateUnit ℚ_[3] (quotientRestrictionScalarsEquiv ℚ_[3] P))) = _
    rw [mapped_conjugate, ord_conjugate]
    rfl

/-- The integral logarithm has coordinates `ord_w`, without division by ramification. -/
theorem localCocharacter_coordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    coordinates (localCocharacter ℚ_[3] place.toRingHom RamifiedLocalModel.integerValuation P) =
      ((RamifiedLocalModel.ord (localPoint P) : ℚ),
        (RamifiedLocalModel.ord (localPoint P) : ℚ)) := by
  rw [localCocharacter, basisValuations_eq, CocharacterIsomorphism.coordinates_fromCyclotomic]
  ext <;> dsimp <;> ring

/-- The norm-defined coordinates in the Fourier height are the character-defined
logarithm divided by two, on the whole local group. -/
theorem rayCoordinates_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    let n := coordinates
      (localCocharacter ℚ_[3] place.toRingHom RamifiedLocalModel.integerValuation P)
    RamifiedLocalModel.rayCoordinates (localPoint P) =
      LocalDegreeNormalization.normalizedValuation 2 ((n.1 : ℝ), (n.2 : ℝ)) := by
  dsimp only
  rw [localCocharacter_coordinates]
  ext <;> simp [RamifiedLocalModel.rayCoordinates,
    RamifiedLocalModel.logarithmicOrder_eq_ord_div_two,
    LocalDegreeNormalization.normalizedValuation, div_eq_mul_inv, mul_comm]

/-- The inverse height uses the positive support-function exponent and exactly one
factor `1/2`, derived from the character-defined logarithm. -/
theorem inverseHeight_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) (s₀ σ : ℂ) :
    let n := coordinates
      (localCocharacter ℚ_[3] place.toRingHom RamifiedLocalModel.integerValuation P)
    RamifiedLocalModel.inverseHeight s₀ σ (localPoint P) =
      (3 : ℂ) ^ (supportFunction s₀ σ ((n.1 : ℝ), (n.2 : ℝ)) / 2) := by
  dsimp only
  rw [RamifiedLocalModel.inverseHeight, rayCoordinates_eq,
    LocalDegreeNormalization.supportFunction_normalizedValuation]
  norm_num

/-- The spectral exponent uses the same single ramification division as the height. -/
theorem character_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) (t : ℝ) :
    let n := coordinates
      (localCocharacter ℚ_[3] place.toRingHom RamifiedLocalModel.integerValuation P)
    RamifiedLocalModel.character t (localPoint P) =
      Circle.exp (-Real.pi * t * Real.log 3 * (((n.1 : ℝ) + (n.2 : ℝ)) / 2)) := by
  dsimp only
  rw [localCocharacter_coordinates]
  change Circle.exp (-Real.pi * t * Real.log 3 * RamifiedLocalModel.degree (localPoint P)) = _
  rw [RamifiedLocalModel.degree_eq_ord]
  congr 1
  push_cast
  ring

end Cubic.ToricHeights.RamifiedQuotientLogarithm
