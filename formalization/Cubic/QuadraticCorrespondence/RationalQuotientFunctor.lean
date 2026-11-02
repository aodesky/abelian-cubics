import Cubic.QuadraticCorrespondence.RationalCoverFunctor

/-!
# Restriction to the rational cyclic invariant ring

Restrict the original cover's rational points to the descended invariant
coordinate ring. The restriction is natural and constant on cyclic orbits.
In the restriction-of-scalars coordinates its formula is
`u ↦ u² / γu`, agreeing with the paper's quotient-character lattice.

The target consists of all algebra-valued points of the invariant ring,
which need not lift to the cover.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.RationalQuotientFunctor

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicCoverDescent CyclotomicPointDescent
open CyclotomicRestrictionScalars RationalCoverFunctor SplitCoverFunctor SplitLaurentInvariants
open Cubic.OrbitParametrization.CyclicGroupAlgebra

/-- Inclusion of the doubly invariant functions in the rational cover ring. -/
def quotientInclusion : quotientFixedRing →ₐ[ℚ] coverFixedRing :=
  Subalgebra.inclusion inf_le_left

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The original cover-to-invariant-ring map on rational coefficient algebras. -/
def quotientPoint (g : traceOneUnits A) : quotientFixedRing →ₐ[ℚ] A :=
  (rationalCoverPointEquiv A g).comp quotientInclusion

theorem quotientPoint_mapUnits {A' : Type*} [CommRing A'] [Algebra ℚ A']
    (φ : A →ₐ[ℚ] A') (g : traceOneUnits A) :
    quotientPoint A' (mapUnits φ.toRingHom g) = φ.comp (quotientPoint A g) := by
  simp only [quotientPoint, rationalCoverPointEquiv_mapUnits, AlgHom.comp_assoc]

/-- Scalar extension of restriction is the restriction of the original split cover. -/
theorem quotientPoint_baseChange (g : traceOneUnits A) (b : quotientFixedRing) :
    (1 : E) ⊗ₜ[ℚ] quotientPoint A g b =
      restrictPoint zeta zeta_relation (extendCover A g) ⟨b, b.property.2⟩ := by
  change (1 : E) ⊗ₜ[ℚ] rationalCoverPointEquiv A g (quotientInclusion b) = _
  rw [← extendPoint_fixed, extend_rationalCoverPoint]
  rfl

/-- Restriction forgets the choice within the original cyclic orbit. -/
theorem quotientPoint_cyclic_mul (i : Multiplicative (ZMod 3)) (g : traceOneUnits A) :
    quotientPoint A (cyclicUnits A i * g) = quotientPoint A g := by
  apply AlgHom.ext
  intro b
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] quotientPoint A (cyclicUnits A i * g) b =
    (1 : E) ⊗ₜ[ℚ] quotientPoint A g b
  rw [quotientPoint_baseChange, quotientPoint_baseChange, map_mul]
  have hi : extendCover A (cyclicUnits A i) = cyclicUnits (E ⊗[ℚ] A) i :=
    mapUnits_cyclicUnits _ i
  rw [hi, restrictPoint_cyclic_mul]

/-- The rational quotient pullback extends to the split quotient-character pullback. -/
theorem extend_quotientPoint (g : traceOneUnits A) :
    extendPoint ((quotientPoint A g).comp fixedRingEquiv.toAlgHom) =
      (coverPointEquiv zeta zeta_relation (extendCover A g)).comp pullbackHom := by
  apply splitPoint_ext
  intro b
  rw [extendPoint_fixed]
  change (1 : E) ⊗ₜ[ℚ] rationalCoverPointEquiv A g (quotientInclusion (fixedRingEquiv b)) = _
  rw [← extendPoint_fixed, extend_rationalCoverPoint]
  rfl

/-- The quotient map has the paper's character formula on the original rational cover. -/
theorem quotientPoint_unit_formula (g : traceOneUnits A) :
    quotientRestrictionScalarsEquiv A (quotientPoint A g) =
      coverUnitEquiv A g ^ 2 / conjugateUnit A (coverUnitEquiv A g) := by
  change (SplitLaurentPoints.coordinates
    (extendPoint ((quotientPoint A g).comp fixedRingEquiv.toAlgHom))).1 = _
  rw [extend_quotientPoint]
  change (SplitCoverFunctor.quotientPointEquiv zeta zeta_relation
    (restrictPoint zeta zeta_relation (extendCover A g))).1 = _
  rw [quotientPointEquiv_restrictPoint]
  have hpair := SplitCoverGalois.charactersOverAlgebra_conjugate zeta zeta_relation
    conjugation conjugation_zeta_sq (baseChangeConjugation A)
    (baseChangeConjugation_algebraMap A) (extendCover A g)
  rw [extendCover_fixed] at hpair
  have hsecond :
      (charactersOverAlgebra zeta zeta_relation (extendCover A g)).2 =
        conjugateUnit A (charactersOverAlgebra zeta zeta_relation (extendCover A g)).1 :=
    congrArg Prod.snd hpair
  rw [hsecond]
  have hfirst : coverUnitEquiv A g =
      (charactersOverAlgebra zeta zeta_relation (extendCover A g)).1 :=
    restrictionScalars_rationalCover A g
  rw [hfirst]

end Cubic.QuadraticCorrespondence.RationalQuotientFunctor
