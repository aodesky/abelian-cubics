import Cubic.OrbitParametrization.CyclicGroupAlgebraMaps
import Cubic.QuadraticCorrespondence.GroupAlgebraSplitting
import Cubic.QuadraticCorrespondence.SplitLaurentPoints
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The original cover represented by the split Laurent ring

Over a characteristic-zero splitting field `K`, every commutative `K`-algebra
`R` has its original augmentation-one group-algebra units naturally identified
with algebra homomorphisms `K[ℤ²] → R`. The construction uses the two
nontrivial characters and works for algebras with nilpotents or zero divisors.
Compatibility with coefficient maps supplies the naturality of this presentation.
The original cyclic action is identified with the diagonal action on the ring;
restricting to invariant functions gives the quotient-character map.
For the cyclotomic field, `RationalCoverFunctor` proves descent of this
presentation to the rational ground field.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitCoverFunctor

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open SplitLaurentInvariants SplitLaurentEvaluation

variable {K : Type*} [Field K] [CharZero K]
variable {R : Type*} [CommRing R] [Algebra K R]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)

omit [CharZero K] in
include hζ in
theorem root_relation : (algebraMap K R ζ) ^ 2 + algebraMap K R ζ + 1 = 0 := by
  simpa using congrArg (algebraMap K R) hζ

/-- The chosen root as a unit, with its polynomially specified inverse. -/
def rootUnit : Kˣ :=
  ⟨ζ, ζ ^ 2, by simpa [pow_succ, mul_comm] using root_cube ζ hζ,
    by simpa [pow_succ] using root_cube ζ hζ⟩

theorem rootUnit_primitive : IsPrimitiveRoot (rootUnit ζ hζ) 3 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  change IsPrimitiveRoot ζ 3
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] using hζ

/-- Character diagonalization for every coefficient algebra of the splitting field. -/
def charactersOverAlgebra : traceOneUnits R ≃* Rˣ × Rˣ := by
  letI : Algebra ℚ R := ((algebraMap K R).comp (algebraMap ℚ K)).toAlgebra
  exact GroupAlgebraSplitting.charactersEquiv (algebraMap K R ζ) (root_relation ζ hζ)

theorem charactersOverAlgebra_apply (g : traceOneUnits R) :
    charactersOverAlgebra ζ hζ g =
      (firstCharacter (algebraMap K R ζ) (root_relation ζ hζ) g,
        secondCharacter (algebraMap K R ζ) (root_relation ζ hζ) g) := rfl

/-- The Laurent ring represents the original augmentation-one unit functor
over the splitting field, rather than merely matching its field-valued points. -/
def coverPointEquiv : traceOneUnits R ≃ (LaurentRing (K := K) →ₐ[K] R) :=
  (charactersOverAlgebra ζ hζ).toEquiv.trans SplitLaurentPoints.pointEquiv.symm

theorem coverPointEquiv_apply (g : traceOneUnits R) :
    coverPointEquiv ζ hζ g = evaluate (charactersOverAlgebra ζ hζ g) := rfl

theorem charactersOverAlgebra_mapUnits {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (g : traceOneUnits R) :
    charactersOverAlgebra ζ hζ (mapUnits φ.toRingHom g) =
      (Units.map φ.toMonoidHom (charactersOverAlgebra ζ hζ g).1,
        Units.map φ.toMonoidHom (charactersOverAlgebra ζ hζ g).2) := by
  apply Prod.ext
  · apply Units.ext
    change (firstCharacter (algebraMap K S ζ) _ (mapUnits φ.toRingHom g) : S) =
      φ (firstCharacter (algebraMap K R ζ) _ g : R)
    simp [firstCharacter, character_val, mapUnits_coefficient, φ.commutes]
  · apply Units.ext
    change (secondCharacter (algebraMap K S ζ) _ (mapUnits φ.toRingHom g) : S) =
      φ (secondCharacter (algebraMap K R ζ) _ g : R)
    simp [secondCharacter_val, mapUnits_coefficient, φ.commutes]

/-- Naturality of the original cover's Laurent presentation. -/
theorem coverPointEquiv_mapUnits {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (g : traceOneUnits R) :
    coverPointEquiv ζ hζ (mapUnits φ.toRingHom g) = φ.comp (coverPointEquiv ζ hζ g) := by
  apply SplitLaurentPoints.pointEquiv.injective
  change SplitLaurentPoints.coordinates (evaluate (charactersOverAlgebra ζ hζ
      (mapUnits φ.toRingHom g))) =
    SplitLaurentPoints.coordinates (φ.comp (evaluate (charactersOverAlgebra ζ hζ g)))
  rw [SplitLaurentPoints.coordinates_evaluate, SplitLaurentPoints.coordinates_comp,
    SplitLaurentPoints.coordinates_evaluate]
  exact charactersOverAlgebra_mapUnits ζ hζ φ g

/-- All cyclic elements act by the expected powers of the two eigenvalues. -/
theorem charactersOverAlgebra_cyclicUnits (i : Multiplicative (ZMod 3)) :
    charactersOverAlgebra ζ hζ (cyclicUnits R i) =
      (Units.map (algebraMap K R).toMonoidHom (rootUnit ζ hζ) ^ i.toAdd.val,
        (Units.map (algebraMap K R).toMonoidHom (rootUnit ζ hζ) ^ i.toAdd.val) ^ 2) := by
  apply Prod.ext
  · apply Units.ext
    change (character R (algebraMap K R ζ) _ (cyclicUnits R i) : R) =
      algebraMap K R ζ ^ i.toAdd.val
    exact character_cyclicUnits R _ _ i
  · apply Units.ext
    change (character R (algebraMap K R ζ ^ 2) _ (cyclicUnits R i) : R) =
      (algebraMap K R ζ ^ i.toAdd.val) ^ 2
    rw [character_cyclicUnits, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem charactersOverAlgebra_cyclic_mul (i : Multiplicative (ZMod 3))
    (g : traceOneUnits R) :
    charactersOverAlgebra ζ hζ (cyclicUnits R i * g) =
      (Units.map (algebraMap K R).toMonoidHom (rootUnit ζ hζ) ^ i.toAdd.val *
          (charactersOverAlgebra ζ hζ g).1,
        (Units.map (algebraMap K R).toMonoidHom (rootUnit ζ hζ) ^ i.toAdd.val) ^ 2 *
          (charactersOverAlgebra ζ hζ g).2) := by
  rw [map_mul, charactersOverAlgebra_cyclicUnits]
  rfl

/-- The diagonal ring action is precisely dual to the original cyclic
action, on points over every commutative coefficient algebra. -/
theorem coverPointEquiv_cyclic_mul (i : Multiplicative (ZMod 3)) (g : traceOneUnits R) :
    coverPointEquiv ζ hζ (cyclicUnits R i * g) =
      (coverPointEquiv ζ hζ g).comp (twist (rootUnit ζ hζ ^ i.toAdd.val)) := by
  apply AlgHom.ext
  intro f
  rw [coverPointEquiv_apply, charactersOverAlgebra_cyclic_mul]
  simpa only [coverPointEquiv_apply, AlgHom.comp_apply, map_pow] using
    (evaluate_twist (rootUnit ζ hζ ^ i.toAdd.val) (charactersOverAlgebra ζ hζ g) f).symm

/-- Restrict a point of the original cover to the invariant coordinate ring. -/
def restrictPoint (g : traceOneUnits R) : invariantRing (rootUnit ζ hζ) →ₐ[K] R :=
  (coverPointEquiv ζ hζ g).comp (invariantRing (rootUnit ζ hζ)).val

theorem restrictPoint_mapUnits {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (g : traceOneUnits R) :
    restrictPoint ζ hζ (mapUnits φ.toRingHom g) = φ.comp (restrictPoint ζ hζ g) := by
  simp only [restrictPoint, coverPointEquiv_mapUnits, AlgHom.comp_assoc]

theorem restrictPoint_cyclic_mul (i : Multiplicative (ZMod 3)) (g : traceOneUnits R) :
    restrictPoint ζ hζ (cyclicUnits R i * g) = restrictPoint ζ hζ g := by
  apply AlgHom.ext
  intro f
  change coverPointEquiv ζ hζ (cyclicUnits R i * g) f = coverPointEquiv ζ hζ g f
  rw [coverPointEquiv_cyclic_mul, AlgHom.comp_apply, twist_pow_apply_of_mem]

/-- The quotient ring of the original split cover has the paper's two
quotient-character coordinates, including points with no lift over `R`. -/
def quotientPointEquiv : (invariantRing (rootUnit ζ hζ) →ₐ[K] R) ≃ Rˣ × Rˣ :=
  SplitLaurentPoints.quotientPointEquiv (rootUnit ζ hζ) (rootUnit_primitive ζ hζ)

theorem quotientPointEquiv_comp {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (F : invariantRing (rootUnit ζ hζ) →ₐ[K] R) :
    quotientPointEquiv ζ hζ (φ.comp F) =
      (Units.map φ.toMonoidHom (quotientPointEquiv ζ hζ F).1,
        Units.map φ.toMonoidHom (quotientPointEquiv ζ hζ F).2) :=
  SplitLaurentPoints.coordinates_comp φ
    (F.comp (invariantEquiv (rootUnit ζ hζ) (rootUnit_primitive ζ hζ)).toAlgHom)

theorem quotientPointEquiv_restrictPoint (g : traceOneUnits R) :
    quotientPointEquiv ζ hζ (restrictPoint ζ hζ g) =
      ((charactersOverAlgebra ζ hζ g).1 ^ 2 / (charactersOverAlgebra ζ hζ g).2,
        (charactersOverAlgebra ζ hζ g).2 ^ 2 / (charactersOverAlgebra ζ hζ g).1) :=
  SplitLaurentPoints.quotientPointEquiv_restrict (rootUnit ζ hζ)
    (rootUnit_primitive ζ hζ) (charactersOverAlgebra ζ hζ g)

end Cubic.QuadraticCorrespondence.SplitCoverFunctor
