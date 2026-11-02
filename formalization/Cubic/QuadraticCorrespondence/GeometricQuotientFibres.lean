import Cubic.QuadraticCorrespondence.RationalQuotientFunctor
import Cubic.QuadraticCorrespondence.QuotientCharacterImage

/-!
# Geometric fibres of the original rational quotient

The scalar-extension isomorphism and the proved character-map fibres identify
the fibres of the rational invariant-ring map with cyclic orbits.
Over an algebraically closed field every quotient point lifts. Rational points
are not assumed to lift over the rational field.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.GeometricQuotientFibres

open scoped TensorProduct
open CyclotomicField CyclotomicTorusGalois CyclotomicTorusDescent
open CyclotomicCoverDescent RationalQuotientFunctor SplitCoverFunctor
open SplitLaurentInvariants
open Cubic.OrbitParametrization.CyclicGroupAlgebra

variable {K : Type*} [Field K]
  [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

/-- Evaluate a scalar extension in the chosen splitting-field algebra. -/
def collapse : E ⊗[ℚ] K →ₐ[E] K :=
  Algebra.TensorProduct.lift (Algebra.ofId E K) (AlgHom.id ℚ K)
    (fun _ _ => Commute.all _ _)

theorem collapse_one_tmul (x : K) : collapse ((1 : E) ⊗ₜ[ℚ] x) = x := by
  simp [collapse, Algebra.TensorProduct.lift_tmul]

theorem collapse_extendCover (g : traceOneUnits K) :
    mapUnits (collapse (K := K)).toRingHom (extendCover K g) = g := by
  apply Subtype.ext
  apply Units.ext
  ext i
  simp [extendCover, mapUnits_coefficient, collapse, Algebra.TensorProduct.lift_tmul]

/-- Extend a point to the split invariant ring using the base-change map. -/
def extendQuotient (p : quotientFixedRing →ₐ[ℚ] K) :
    invariantRing (rootUnit zeta zeta_relation) →ₐ[E] K :=
  (Algebra.TensorProduct.lift (Algebra.ofId E K) p (fun _ _ => Commute.all _ _)).comp
    quotientBaseChangeEquiv.symm.toAlgHom

theorem extendQuotient_fixed (p : quotientFixedRing →ₐ[ℚ] K) (b : quotientFixedRing) :
    extendQuotient p ⟨b, b.property.2⟩ = p b := by
  have hb : quotientBaseChangeEquiv.symm ⟨b, b.property.2⟩ = (1 : E) ⊗ₜ[ℚ] b := by
    apply quotientBaseChangeEquiv.injective
    apply Subtype.ext
    simp
  simp [extendQuotient, hb, Algebra.TensorProduct.lift_tmul]

theorem extendQuotient_injective : Function.Injective (extendQuotient (K := K)) := by
  intro p q h
  apply AlgHom.ext
  intro b
  simpa only [extendQuotient_fixed] using
    congrArg (fun f => f ⟨b, b.property.2⟩) h

/-- The rational and split restrictions agree on the original cover. -/
theorem quotientPoint_eq_restrict (g : traceOneUnits K) (b : quotientFixedRing) :
    quotientPoint K g b = restrictPoint zeta zeta_relation g ⟨b, b.property.2⟩ := by
  have h := congrArg (collapse (K := K)) (quotientPoint_baseChange K g b)
  have hmap := restrictPoint_mapUnits zeta zeta_relation (collapse (K := K))
    (extendCover K g)
  rw [collapse_extendCover] at hmap
  rw [collapse_one_tmul] at h
  rw [h]
  exact (congrArg (fun f => f ⟨b, b.property.2⟩) hmap).symm

theorem extendQuotient_quotientPoint (g : traceOneUnits K) :
    extendQuotient (quotientPoint K g) = restrictPoint zeta zeta_relation g := by
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := quotientBaseChangeEquiv.surjective b
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have he : quotientBaseChangeEquiv (c ⊗ₜ[ℚ] b) =
        c • (⟨b, b.property.2⟩ : invariantRing (rootUnit zeta zeta_relation)) := by
      apply Subtype.ext
      exact quotientBaseChangeEquiv_tmul c b
    rw [he, map_smul, map_smul, extendQuotient_fixed, quotientPoint_eq_restrict]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [CharZero K]

/-- Fibres on geometric points are exactly the original cyclic orbits. -/
theorem quotientPoint_eq_iff (g h : traceOneUnits K) :
    quotientPoint K g = quotientPoint K h ↔ ∃ i, g = cyclicUnits K i * h := by
  rw [← (extendQuotient_injective (K := K)).eq_iff,
    extendQuotient_quotientPoint, extendQuotient_quotientPoint,
    ← (quotientPointEquiv zeta zeta_relation).injective.eq_iff,
    quotientPointEquiv_restrictPoint, quotientPointEquiv_restrictPoint]
  exact CharacterCoefficients.quotientCharacters_eq_iff
    (algebraMap E K zeta) (root_relation zeta zeta_relation) g h

/-- Every geometric quotient point lifts; the corresponding rational statement is false. -/
theorem quotientPoint_surjective [IsAlgClosed K] : Function.Surjective (quotientPoint K) := by
  intro p
  obtain ⟨g, hg⟩ := CharacterCoefficients.quotientCharacters_surjective
    (algebraMap E K zeta) (root_relation zeta zeta_relation)
      (quotientPointEquiv zeta zeta_relation (extendQuotient p))
  refine ⟨g, extendQuotient_injective ?_⟩
  rw [extendQuotient_quotientPoint]
  apply (quotientPointEquiv zeta zeta_relation).injective
  rw [quotientPointEquiv_restrictPoint]
  exact hg

end Cubic.QuadraticCorrespondence.GeometricQuotientFibres
