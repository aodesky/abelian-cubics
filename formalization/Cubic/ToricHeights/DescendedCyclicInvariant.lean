import Cubic.QuadraticCorrespondence.DescendedCoefficients

/-!
# The original cyclic invariant and its monic quadratic

The paper's `δ=X²Y+Y²Z+Z²X` on the trace-one cover descends to the
quotient ring. Its monic quadratic has coefficients in the two original cubic
coefficient functions. This is the algebraic input for checking that `δ`
adds no further p-adic integrality condition. Generation of the entire integral
invariant ring is `eqn:affineC3invariants` (`AffineC3Invariants`).
-/

noncomputable section

namespace Cubic.ToricHeights.DescendedCyclicInvariant

open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField
open CyclotomicTorusGalois DescendedCoefficients SplitCoverFunctor
open SplitLaurentInvariants
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CyclicGroupAlgebra

private theorem universal_evaluation :
    coverPointEquiv zeta zeta_relation universalCover = AlgHom.id E CoverRing :=
  (coverPointEquiv zeta zeta_relation).apply_symm_apply _

/-- The original coordinates are defined over the rational ground field. -/
theorem coverCoordinate_conjugation (i : ZMod 3) :
    SplitLaurentGalois.conjugate conjugation (coverCoordinate i) = coverCoordinate i := by
  let γ := SplitLaurentGalois.conjugate conjugation
  have hu : mapUnits γ.toRingHom universalCover = universalCover := by
    apply (coverPointEquiv zeta zeta_relation).injective
    apply AlgHom.ext
    intro f
    obtain ⟨b, rfl⟩ := γ.surjective f
    have h := SplitCoverGalois.coverPointEquiv_conjugate zeta zeta_relation conjugation
      conjugation_zeta_sq γ (SplitLaurentGalois.conjugate_algebraMap conjugation) universalCover b
    simpa only [universal_evaluation, AlgHom.id_apply] using h
  have h := congrArg (fun g : traceOneUnits CoverRing => (g.val : GroupAlgebra CoverRing) i) hu
  simpa only [mapUnits_coefficient] using h

/-- The cyclic generator rotates the original coordinate functions. -/
theorem coverCoordinate_twist (i : ZMod 3) :
    twist (rootUnit zeta zeta_relation) (coverCoordinate i) = coverCoordinate (-1 + i) := by
  have h := congrArg (fun f : CoverRing →ₐ[E] CoverRing => f (coverCoordinate i))
    (coverPointEquiv_cyclic_mul zeta zeta_relation (Multiplicative.ofAdd (1 : ZMod 3)) universalCover)
  dsimp only at h
  rw [evaluate_coverCoordinate, universal_evaluation] at h
  have hi : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = 1 := by decide
  simp only [AlgHom.comp_apply, AlgHom.id_apply, hi, pow_one, Subgroup.coe_mul, Units.val_mul] at h
  change (AddMonoidAlgebra.single (1 : ZMod 3) (1 : CoverRing) *
    (universalCover.val : GroupAlgebra CoverRing)) i =
      twist (rootUnit zeta zeta_relation) (coverCoordinate i) at h
  simpa only [AddMonoidAlgebra.single_mul_apply, one_mul] using h.symm

/-- The third regular function in the paper's local integrality definition. -/
def coverDelta : CoverRing :=
  coverCoordinate 0 ^ 2 * coverCoordinate 1 +
    coverCoordinate 1 ^ 2 * coverCoordinate 2 + coverCoordinate 2 ^ 2 * coverCoordinate 0

theorem coverDelta_fixed : coverDelta ∈ quotientFixedRing := by
  constructor
  · change SplitLaurentGalois.conjugate conjugation coverDelta = coverDelta
    simp only [coverDelta, map_add, map_mul, map_pow, coverCoordinate_conjugation]
  · change twist (rootUnit zeta zeta_relation) coverDelta = coverDelta
    simp only [coverDelta, map_add, map_mul, map_pow, coverCoordinate_twist]
    norm_num
    rw [show (-1 : ZMod 3) = 2 by decide]
    ring

/-- The original cyclic invariant, with both descent conditions proved. -/
def delta : quotientFixedRing := ⟨coverDelta, coverDelta_fixed⟩

/-- On the original rational cover this is precisely the cyclic polynomial in its coordinates. -/
theorem quotientPoint_delta {A : Type*} [CommRing A] [Algebra ℚ A] (g : traceOneUnits A) :
    RationalQuotientFunctor.quotientPoint A g delta =
      ((g.val : GroupAlgebra A) 0) ^ 2 * (g.val : GroupAlgebra A) 1 +
        ((g.val : GroupAlgebra A) 1) ^ 2 * (g.val : GroupAlgebra A) 2 +
        ((g.val : GroupAlgebra A) 2) ^ 2 * (g.val : GroupAlgebra A) 0 := by
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] RationalQuotientFunctor.quotientPoint A g delta = _
  rw [RationalQuotientFunctor.quotientPoint_baseChange]
  change coverPointEquiv zeta zeta_relation (CyclotomicCoverDescent.extendCover A g) coverDelta = _
  simp only [coverDelta, map_add, map_mul, map_pow, evaluate_coverCoordinate,
    CyclotomicCoverDescent.extendCover, mapUnits_coefficient]
  rfl

/-- The monic quadratic, with `a=e₂` and `b=-e₃` as in the characteristic polynomial. -/
theorem delta_quadratic :
    delta ^ 2 = (linearCoefficient + 3 * constantCoefficient) * delta -
      (linearCoefficient ^ 3 - constantCoefficient + 9 * constantCoefficient ^ 2 +
        6 * linearCoefficient * constantCoefficient) := by
  apply Subtype.ext
  change coverDelta ^ 2 = (coverLinearCoefficient + 3 * coverConstantCoefficient) * coverDelta -
    (coverLinearCoefficient ^ 3 - coverConstantCoefficient + 9 * coverConstantCoefficient ^ 2 +
      6 * coverLinearCoefficient * coverConstantCoefficient)
  have ht := trace_one CoverRing universalCover
  change coverCoordinate 0 + coverCoordinate 1 + coverCoordinate 2 = 1 at ht
  have hz : coverCoordinate 2 = 1 - coverCoordinate 0 - coverCoordinate 1 := by
    linear_combination ht
  simp only [coverDelta, coverLinearCoefficient, coverConstantCoefficient, secondCoeff, constantCoeff, hz]
  ring

/-- The relation holds on all quotient points, whether or not they lift to the cover. -/
theorem delta_quadratic_at {A : Type*} [CommRing A] [Algebra ℚ A]
    (P : quotientFixedRing →ₐ[ℚ] A) :
    P delta ^ 2 = (P linearCoefficient + 3 * P constantCoefficient) * P delta -
      (P linearCoefficient ^ 3 - P constantCoefficient + 9 * P constantCoefficient ^ 2 +
        6 * P linearCoefficient * P constantCoefficient) := by
  simpa only [map_pow, map_sub, map_add, map_mul, map_ofNat] using congrArg P delta_quadratic

end Cubic.ToricHeights.DescendedCyclicInvariant
