import Cubic.QuadraticCorrespondence.QuotientLocalCharacters
import Cubic.QuadraticCorrespondence.CyclotomicBaseChange
import Cubic.ToricHeights.SplitLocalHeight

/-!
# Character-defined logarithms at split local places

The two local embeddings send the global root to the chosen p-adic root and
its conjugate. Evaluating the original quotient characters through the first
embedding gives the two coordinate valuations used by the split Fourier model.
Their ray coordinates have the thirds dictated by the enlarged lattice.

The comparison concerns arbitrary descended quotient points, before the
integral cutoff. It is a local statement; the adelic height is assembled in
`Cubic.PoissonSummation.FiniteAdelicData`.
-/

noncomputable section

namespace Cubic.ToricHeights.SplitQuotientLogarithm

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois CyclotomicRestrictionScalars QuotientLocalCharacters
open Cubic.OrbitParametrization.CocharacterLattice
open Cubic.OrbitParametrization

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]

/-- Split the tensor algebra using the chosen local cube root of unity. -/
def splitting : E ⊗[ℚ] ℚ_[p] ≃ₐ[ℚ] ℚ_[p] × ℚ_[p] :=
  (CyclotomicBaseChange.paperPresentation ℚ_[p]).trans
    ((CyclotomicLocalAlgebra.padicSplittingEquiv p Fact.out).restrictScalars ℚ)

theorem splitting_zeta : splitting p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p])) =
    (Classical.choose (CyclotomicLocalRoots.field_root p Fact.out),
      -1 - Classical.choose (CyclotomicLocalRoots.field_root p Fact.out)) := by
  simp [splitting, CyclotomicLocalAlgebra.padicSplittingEquiv]

@[simp]
theorem splitting_scalar (a : ℚ_[p]) : splitting p ((1 : E) ⊗ₜ[ℚ] a) = (a, a) := by
  simp [splitting, CyclotomicBaseChange.paperPresentation,
    CyclotomicBaseChange.presentation]
  exact (CyclotomicLocalAlgebra.padicSplittingEquiv p Fact.out).commutes a

/-- Swapping the two places, as an automorphism of rational algebras. -/
def swapPlaces : (ℚ_[p] × ℚ_[p]) ≃ₐ[ℚ] (ℚ_[p] × ℚ_[p]) :=
  { RingEquiv.prodComm with commutes' := fun _ => rfl }

theorem splitting_conjugation (x : E ⊗[ℚ] ℚ_[p]) :
    splitting p (baseChangeConjugation ℚ_[p] x) = (splitting p x).swap := by
  apply map_baseChangeConjugation ℚ_[p] (splitting p).toAlgHom (swapPlaces p)
  · change (splitting p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p]))).swap =
      -1 - splitting p (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℚ_[p]))
    rw [splitting_zeta]
    ext <;> dsimp
    ring
  · intro a
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, splitting_scalar]
    rfl

/-- The chosen first place; the conjugate character will use the other factor. -/
def place : E ⊗[ℚ] ℚ_[p] →+* ℚ_[p] :=
  (RingHom.fst ℚ_[p] ℚ_[p]).comp (splitting p).toRingHom

/-- Both local unit coordinates of an arbitrary descended quotient point. -/
def localPoint (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : SplitLocalModel.Points p :=
  MulEquiv.prodUnits (Units.map (splitting p).toMonoidHom
    (quotientRestrictionScalarsEquiv ℚ_[p] P))

theorem mapped_conjugate (u : (E ⊗[ℚ] ℚ_[p])ˣ) :
    Units.map (place p).toMonoidHom (conjugateUnit ℚ_[p] u) =
      (MulEquiv.prodUnits (Units.map (splitting p).toMonoidHom u)).2 := by
  apply Units.ext
  change (splitting p (baseChangeConjugation ℚ_[p] (u : E ⊗[ℚ] ℚ_[p]))).1 = _
  rw [splitting_conjugation]
  rfl

/-- The basis-character valuations are the two p-adic coordinate valuations. -/
theorem basisValuations_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    basisValuations ℚ_[p] (place p) (PadicMultiplicative.valuation p) P =
      (Padic.valuation ((localPoint p P).1 : ℚ_[p]),
        Padic.valuation ((localPoint p P).2 : ℚ_[p])) := by
  apply Prod.ext
  · rfl
  · change (PadicMultiplicative.valuation p
      (Units.map (place p).toMonoidHom
        (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P)))).toAdd = _
    rw [mapped_conjugate]
    rfl

/-- The other split place is evaluation in the second local factor. -/
def secondPlace : E ⊗[ℚ] ℚ_[p] →+* ℚ_[p] :=
  (RingHom.snd ℚ_[p] ℚ_[p]).comp (splitting p).toRingHom

theorem secondPlace_unit (u : (E ⊗[ℚ] ℚ_[p])ˣ) :
    Units.map (secondPlace p).toMonoidHom u =
      Units.map (place p).toMonoidHom (conjugateUnit ℚ_[p] u) := by
  apply Units.ext
  change (splitting p (u : E ⊗[ℚ] ℚ_[p])).2 =
    (splitting p (baseChangeConjugation ℚ_[p] (u : E ⊗[ℚ] ℚ_[p]))).1
  rw [splitting_conjugation]
  rfl

/-- Switching the place switches the two basis-character valuations. -/
theorem basisValuations_secondPlace (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    basisValuations ℚ_[p] (secondPlace p) (PadicMultiplicative.valuation p) P =
      (basisValuations ℚ_[p] (place p) (PadicMultiplicative.valuation p) P).swap := by
  simp only [basisValuations, secondPlace_unit]
  rw [conjugateUnit_involutive ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P)]
  rfl

/-- The second place's character-defined cocharacter swaps the paper's ray coordinates. -/
theorem secondPlace_coordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    coordinates (localCocharacter ℚ_[p] (secondPlace p) (PadicMultiplicative.valuation p) P) =
      (coordinates (localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P)).swap := by
  rw [localCocharacter, basisValuations_secondPlace, localCocharacter]
  simp only [CocharacterIsomorphism.coordinates_fromCyclotomic]
  ext <;> dsimp <;> ring

/-- The original character pairing determines exactly the model's enlarged-lattice valuation. -/
theorem localCocharacter_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P =
      (SplitLocalModel.valuation p (localPoint p P)).toAdd := by
  rw [localCocharacter, basisValuations_eq]
  rfl

/-- The thirds in the height coordinates are the inverse character-lattice matrix,
not a ramification factor. -/
theorem localCocharacter_coordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    let a := Padic.valuation ((localPoint p P).1 : ℚ_[p])
    let b := Padic.valuation ((localPoint p P).2 : ℚ_[p])
    coordinates (localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P) =
      ((2 * (a : ℚ) + b) / 3, ((a : ℚ) + 2 * b) / 3) := by
  dsimp only
  rw [localCocharacter, basisValuations_eq, CocharacterIsomorphism.coordinates_fromCyclotomic]

theorem rayCoordinates_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    let n := coordinates (localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P)
    SplitLocalModel.rayCoordinates p (localPoint p P) = ((n.1 : ℝ), (n.2 : ℝ)) := by
  dsimp only
  rw [localCocharacter_eq]
  rfl

/-- The full inverse height uses the character-defined cocharacter before any Galois average. -/
theorem inverseHeight_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (s₀ σ : ℂ) :
    let n := coordinates (localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P)
    SplitLocalModel.inverseHeight p s₀ σ (localPoint p P) =
      (p : ℂ) ^ supportFunction s₀ σ ((n.1 : ℝ), (n.2 : ℝ)) := by
  dsimp only
  rw [SplitLocalModel.inverseHeight, rayCoordinates_eq]

/-- The spectral exponent uses the sum of the ray coordinates with the paper's sign. -/
theorem character_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (t : ℝ) :
    let n := coordinates (localCocharacter ℚ_[p] (place p) (PadicMultiplicative.valuation p) P)
    SplitLocalModel.character p t (localPoint p P) =
      Circle.exp (-Real.pi * t * Real.log p * ((n.1 : ℝ) + (n.2 : ℝ))) := by
  dsimp only
  have h := SplitLocalModel.rayCoordinates_sum p (localPoint p P)
  rw [rayCoordinates_eq] at h
  change Circle.exp (-Real.pi * t * Real.log p *
    (SplitLocalModel.degree p (localPoint p P) : ℝ)) = _
  rw [← h]

end Cubic.ToricHeights.SplitQuotientLogarithm
