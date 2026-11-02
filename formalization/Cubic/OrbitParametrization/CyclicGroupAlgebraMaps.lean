import Cubic.OrbitParametrization.CyclicGroupAlgebra

/-!
# Change of coefficients in the cyclic group algebra

Coefficient ring homomorphisms preserve augmentation-one units and the embedded
cyclic subgroup. Evaluation at a cube root commutes with change of coefficients.
These maps supply the original cover's functoriality, before taking its quotient.
-/

noncomputable section

namespace Cubic.OrbitParametrization.CyclicGroupAlgebra

variable {R S U : Type*} [CommRing R] [CommRing S] [CommRing U]

theorem augmentation_mapRange (φ : R →+* S) (f : GroupAlgebra R) :
    augmentation S (AddMonoidAlgebra.mapRangeRingHom (ZMod 3) φ f) =
      φ (augmentation R f) := by
  simp [augmentation_coefficients, AddMonoidAlgebra.mapRangeRingHom_apply]

/-- The original cover's map induced by a coefficient ring homomorphism. -/
def mapUnits (φ : R →+* S) : traceOneUnits R →* traceOneUnits S :=
  ((Units.map (AddMonoidAlgebra.mapRangeRingHom (ZMod 3) φ).toMonoidHom).comp
    (traceOneUnits R).subtype).codRestrict (traceOneUnits S) (by
      intro g
      apply Units.ext
      change augmentation S (AddMonoidAlgebra.mapRangeRingHom (ZMod 3) φ
        (g.val : GroupAlgebra R)) = 1
      rw [augmentation_mapRange, augmentation_traceOneUnit, map_one])

theorem mapUnits_coefficient (φ : R →+* S) (g : traceOneUnits R) (i : ZMod 3) :
    ((mapUnits φ g).val : GroupAlgebra S) i = φ ((g.val : GroupAlgebra R) i) :=
  AddMonoidAlgebra.mapRangeRingHom_apply φ _ i

theorem mapUnits_id (g : traceOneUnits R) : mapUnits (RingHom.id R) g = g := by
  apply Subtype.ext
  apply Units.ext
  ext i
  simp [mapUnits_coefficient]

theorem mapUnits_comp (ψ : S →+* U) (φ : R →+* S) (g : traceOneUnits R) :
    mapUnits (ψ.comp φ) g = mapUnits ψ (mapUnits φ g) := by
  apply Subtype.ext
  apply Units.ext
  ext i
  simp [mapUnits_coefficient]

theorem mapUnits_cyclicUnits (φ : R →+* S) (i : Multiplicative (ZMod 3)) :
    mapUnits φ (cyclicUnits R i) = cyclicUnits S i := by
  apply Subtype.ext
  apply Units.ext
  change AddMonoidAlgebra.mapRangeRingHom (ZMod 3) φ
    (AddMonoidAlgebra.single i.toAdd 1) = AddMonoidAlgebra.single i.toAdd 1
  simp

/-- Characters of the original cover commute with change of coefficients. -/
theorem character_mapUnits (φ : R →+* S) (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : traceOneUnits R) :
    character S (φ ζ) (by simpa using congrArg φ hζ) (mapUnits φ g) =
      Units.map φ.toMonoidHom (character R ζ hζ g) := by
  apply Units.ext
  simp [character_val, mapUnits_coefficient]

end Cubic.OrbitParametrization.CyclicGroupAlgebra
