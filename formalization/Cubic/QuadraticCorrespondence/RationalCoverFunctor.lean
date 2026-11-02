import Cubic.QuadraticCorrespondence.CyclotomicCoverDescent
import Cubic.QuadraticCorrespondence.CyclotomicRestrictionScalars

/-!
# The rational fixed ring represents the original cover

For every commutative rational algebra, the original augmentation-one units
are naturally identified with points of the descended cover ring. Combining
this with the restriction-of-scalars coordinates gives a group
isomorphism with the units of the quadratic scalar extension.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalCoverFunctor

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicCoverDescent
open CyclotomicPointDescent CyclotomicRestrictionScalars SplitCoverFunctor SplitLaurentInvariants
open Cubic.OrbitParametrization.CyclicGroupAlgebra

variable (A : Type*) [CommRing A] [Algebra ℚ A]

theorem fixed_iff_equivariant (g : traceOneUnits (E ⊗[ℚ] A)) :
    mapUnits (baseChangeConjugation A).toRingHom g = g ↔
      IsEquivariant (coverPointEquiv zeta zeta_relation g) := by
  constructor
  · intro hg b
    simpa only [hg] using coverPoint_baseChangeConjugation A g b
  · intro hg
    apply (coverPointEquiv zeta zeta_relation).injective
    apply AlgHom.ext
    intro b
    obtain ⟨c, rfl⟩ := (SplitLaurentGalois.conjugate conjugation).surjective b
    exact (coverPoint_baseChangeConjugation A g c).trans (hg c).symm

/-- The original split cover and Laurent-ring presentation have the same descent data. -/
def fixedPointEquiv : fixedCover A ≃
    {f : LaurentRing (K := E) →ₐ[E] E ⊗[ℚ] A // IsEquivariant f} :=
  (coverPointEquiv zeta zeta_relation).subtypeEquiv (fixed_iff_equivariant A)

/-- The fixed coordinate ring represents the original cover over the rational field. -/
def rationalCoverPointEquiv : traceOneUnits A ≃ (coverFixedRing →ₐ[ℚ] A) :=
  (fixedCoverEquiv A).toEquiv.trans
    ((fixedPointEquiv A).trans equivariantPointEquiv.symm)

/-- The descended comparison becomes the original character presentation after scalar extension. -/
theorem extend_rationalCoverPoint (g : traceOneUnits A) :
    extendPoint (rationalCoverPointEquiv A g) =
      coverPointEquiv zeta zeta_relation (extendCover A g) :=
  extend_descend _ _

/-- The representation is natural over all commutative rational coefficient algebras. -/
theorem rationalCoverPointEquiv_mapUnits {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (g : traceOneUnits A) :
    rationalCoverPointEquiv A' (mapUnits φ.toRingHom g) =
      φ.comp (rationalCoverPointEquiv A g) := by
  apply extendPoint_injective
  rw [extendPoint_comp, extend_rationalCoverPoint, extend_rationalCoverPoint,
    extendCover_mapUnits, coverPointEquiv_mapUnits]

/-- The scalar-extension unit is the first character of the original cover. -/
theorem restrictionScalars_rationalCover (g : traceOneUnits A) :
    restrictionScalarsEquiv A (rationalCoverPointEquiv A g) =
      (charactersOverAlgebra zeta zeta_relation (extendCover A g)).1 := by
  change (SplitLaurentPoints.coordinates (extendPoint (rationalCoverPointEquiv A g))).1 = _
  rw [extend_rationalCoverPoint, coverPointEquiv_apply, SplitLaurentPoints.coordinates_evaluate]

/-- The cover itself is naturally the restriction-of-scalars multiplicative group. -/
def coverUnitEquiv : traceOneUnits A ≃* (E ⊗[ℚ] A)ˣ :=
  { (rationalCoverPointEquiv A).trans (restrictionScalarsEquiv A) with
    map_mul' := by
      intro g h
      change restrictionScalarsEquiv A (rationalCoverPointEquiv A (g * h)) = _
      rw [restrictionScalars_rationalCover, map_mul, map_mul]
      exact congrArg₂ (· * ·) (restrictionScalars_rationalCover A g).symm
        (restrictionScalars_rationalCover A h).symm }

theorem coverUnitEquiv_mapUnits {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (g : traceOneUnits A) :
    coverUnitEquiv A' (mapUnits φ.toRingHom g) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom (coverUnitEquiv A g) := by
  change restrictionScalarsEquiv A' (rationalCoverPointEquiv A' (mapUnits φ.toRingHom g)) = _
  rw [rationalCoverPointEquiv_mapUnits, restrictionScalarsEquiv_comp]
  rfl

end Cubic.QuadraticCorrespondence.RationalCoverFunctor
