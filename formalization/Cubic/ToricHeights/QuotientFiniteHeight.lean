import Cubic.ToricHeights.QuotientLocalModels
import Cubic.ToricHeights.LocalLogarithmNormalization

/-!
# Splitting-field contributions on the original finite quotient points

Evaluate the original character-defined cocharacters at the local
places. Use the residue cardinalities of their integer rings and the global
degree `[E:ℚ]` to form the local height factors and logarithmic contributions.
At a split prime there are two contributions; the support function is evaluated
on each cocharacter before multiplying height factors. Its nonlinear value is
never replaced by its value on the averaged logarithm.

The comparisons with the local Fourier models are proved below. The adelic
height and character are assembled from these local data in
`Cubic.PoissonSummation.FiniteAdelicData`.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientFiniteHeight

open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois QuotientLocalCharacters
open Cubic.OrbitParametrization
open Cubic.OrbitParametrization.CocharacterLattice
open LocalLogarithmNormalization

variable (p : ℕ) [Fact p.Prime]

/-- Real ray coordinates of the integral character-defined cocharacter. -/
def realCoordinates (n : ℤ × ℤ) : ℝ × ℝ :=
  ((coordinates n).1, (coordinates n).2)

section Split

variable [Fact (p % 3 = 1)]

def splitCoordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  realCoordinates (localCocharacter ℚ_[p] (SplitQuotientLogarithm.place p)
    (PadicMultiplicative.valuation p) P)

def splitSecondCoordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  realCoordinates (localCocharacter ℚ_[p] (SplitQuotientLogarithm.secondPlace p)
    (PadicMultiplicative.valuation p) P)

theorem splitSecondCoordinates_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitSecondCoordinates p P = (splitCoordinates p P).swap := by
  unfold splitSecondCoordinates splitCoordinates realCoordinates
  rw [SplitQuotientLogarithm.secondPlace_coordinates]
  rfl

/-- Two splitting-field factors, weighted by the global degree.
The sign is positive because this is `H(P,-s)`. -/
def splitInverseHeight (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^
      (supportFunction s₀ σ (splitCoordinates p P) / Module.finrank ℚ E) *
    (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^
      (supportFunction s₀ σ (splitSecondCoordinates p P) / Module.finrank ℚ E)

/-- The two place contributions to the adelic logarithm, before applying a character. -/
def splitLogarithm (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  placeContribution (Module.finrank ℚ E) (Nat.card (IsLocalRing.ResidueField ℤ_[p]))
      (splitCoordinates p P) +
    placeContribution (Module.finrank ℚ E) (Nat.card (IsLocalRing.ResidueField ℤ_[p]))
      (splitSecondCoordinates p P)

theorem splitInverseHeight_eq (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitInverseHeight p s₀ σ P =
      SplitLocalModel.inverseHeight p s₀ σ (SplitQuotientLogarithm.localPoint p P) := by
  rw [splitInverseHeight, padic_residue_cardinality, CyclotomicField.finrank_eq_two,
    splitSecondCoordinates_eq]
  simp only [Nat.cast_ofNat]
  have h := LocalDegreeNormalization.split_height_product p (-s₀) (-σ) (splitCoordinates p P)
  simp only [supportFunction_neg, neg_neg] at h
  rw [h, SplitQuotientLogarithm.inverseHeight_eq]
  rfl

theorem splitLogarithm_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitLogarithm p P = conjugateAverage (normalizedLog p
      (SplitLocalModel.rayCoordinates p (SplitQuotientLogarithm.localPoint p P))) := by
  rw [splitLogarithm, CyclotomicField.finrank_eq_two, splitSecondCoordinates_eq,
    split_residue_placeContributions, SplitQuotientLogarithm.rayCoordinates_eq]
  rfl

end Split

section Inert

variable [Fact (p % 3 = 2)]

def inertCoordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  realCoordinates (localCocharacter ℚ_[p] (InertQuotientLogarithm.place p).toRingHom
    (InertLocalModel.integerValuation p) P)

/-- The single inert residue-field factor, with global degree two. -/
def inertInverseHeight (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)) : ℂ) ^
    (supportFunction s₀ σ (inertCoordinates p P) / Module.finrank ℚ E)

def inertLogarithm (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℝ × ℝ :=
  placeContribution (Module.finrank ℚ E)
    (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p))) (inertCoordinates p P)

theorem inertInverseHeight_eq (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertInverseHeight p s₀ σ P =
      InertLocalModel.inverseHeight p s₀ σ (InertQuotientLogarithm.localPoint p P) := by
  rw [inertInverseHeight, CyclotomicInertField.card_residueField, CyclotomicField.finrank_eq_two,
    Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, InertQuotientLogarithm.inverseHeight_eq]
  congr 1
  change (2 : ℂ) * (supportFunction s₀ σ (inertCoordinates p P) / 2) =
    supportFunction s₀ σ (inertCoordinates p P)
  ring

theorem inertLogarithm_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertLogarithm p P = normalizedLog p
      (InertLocalModel.rayCoordinates p (InertQuotientLogarithm.localPoint p P)) := by
  have hn : inertCoordinates p P =
      ((InertLocalModel.ord p (InertQuotientLogarithm.localPoint p P) : ℝ),
        (InertLocalModel.ord p (InertQuotientLogarithm.localPoint p P) : ℝ)) := by
    exact (InertQuotientLogarithm.rayCoordinates_eq p P).symm.trans
      (inert_rayCoordinates p _)
  rw [inertLogarithm, CyclotomicField.finrank_eq_two, hn]
  exact inert_residue_weightedLog p _

end Inert

def ramifiedCoordinates (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℝ × ℝ :=
  realCoordinates (localCocharacter ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom
    RamifiedLocalModel.integerValuation P)

/-- The single ramified residue-field factor. Its residue cardinality is three,
so division by the global degree survives exactly once. -/
def ramifiedInverseHeight (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers) : ℂ) ^
    (supportFunction s₀ σ (ramifiedCoordinates P) / Module.finrank ℚ E)

def ramifiedLogarithm (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℝ × ℝ :=
  placeContribution (Module.finrank ℚ E)
    (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers)) (ramifiedCoordinates P)

theorem ramifiedInverseHeight_eq (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedInverseHeight s₀ σ P =
      RamifiedLocalModel.inverseHeight s₀ σ (RamifiedQuotientLogarithm.localPoint P) := by
  rw [ramifiedInverseHeight, CyclotomicRamifiedField.card_residueField,
    CyclotomicField.finrank_eq_two, RamifiedQuotientLogarithm.inverseHeight_eq]
  rfl

theorem ramifiedLogarithm_eq (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedLogarithm P = normalizedLog 3
      (RamifiedLocalModel.rayCoordinates (RamifiedQuotientLogarithm.localPoint P)) := by
  have hn : ramifiedCoordinates P =
      ((RamifiedLocalModel.ord (RamifiedQuotientLogarithm.localPoint P) : ℝ),
        (RamifiedLocalModel.ord (RamifiedQuotientLogarithm.localPoint P) : ℝ)) := by
    unfold ramifiedCoordinates realCoordinates
    rw [RamifiedQuotientLogarithm.localCocharacter_coordinates]
    push_cast
    rfl
  rw [ramifiedLogarithm, CyclotomicField.finrank_eq_two, hn]
  exact ramified_residue_weightedLog _

end Cubic.ToricHeights.QuotientFiniteHeight
