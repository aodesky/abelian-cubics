import Cubic.ToricHeights.DescendedCyclicInvariant
import Cubic.QuadraticCorrespondence.QuotientCoefficientFormula

/-!
# The weight vectors of `lemma:heightformula`

The paper defines `√disc = (X-Z)(Y-X)(Z-Y)`. It is invariant under the cyclic
action and defined over `ℚ`, so it descends to the quotient ring, as
`δ` does. The two conjugate cubic characters satisfy

`χ^{2a'+b'} = 1 - 9/2 e₂ + 27/2 e₃ + √-27/2 √disc`,
`χ^{a'+2b'} = 1 - 9/2 e₂ + 27/2 e₃ - √-27/2 √disc`

on the trace-one chart (`eqn:weightVectors`, `eqn:formulaForNormCharacter2`).
On the cover this is the identity `χ₁³ - χ₂³ = √-27 √disc` for the two
nontrivial characters `χ₁ = X+ζY+ζ²Z` and `χ₂ = X+ζ²Y+ζZ`. We then evaluate the
formula at every point of the quotient after any place map, without a cover
lift. In Lean `constantCoefficient = -e₃`.

The paper's "short computation" in `prop:canonicalHeight` is the product
identity `z₊ z₋ = (1-3e₂)³`, which follows from `√disc² = disc`.
-/

noncomputable section

namespace Cubic.ToricHeights.WeightVectors

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField
open CyclotomicTorusGalois DescendedCoefficients SplitCoverFunctor SplitLaurentInvariants
open CyclotomicRestrictionScalars QuotientLocalCharacters QuotientCoefficientFormula
open SplitLaurentEvaluation SplitLaurentPoints CyclotomicPointDescent RationalQuotientGroup
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters DescendedCyclicInvariant

/-- The difference of the two cubic characters, for three arbitrary coordinates. -/
theorem eigenvalue_cubes_difference {R : Type*} [CommRing R] (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (x y z : R) :
    (x + y * ζ + z * ζ ^ 2) ^ 3 - (x + y * ζ ^ 2 + z * ζ) ^ 3 =
      3 * (2 * ζ + 1) * ((x - z) * (y - x) * (z - y)) := by
  linear_combination -(y - z) * (ζ ^ 4 * y ^ 2 + ζ ^ 4 * y * z + ζ ^ 4 * z ^ 2 - ζ ^ 3 * y ^ 2 +
    2 * ζ ^ 3 * y * z - ζ ^ 3 * z ^ 2 + 3 * ζ ^ 2 * x * y + 3 * ζ ^ 2 * x * z -
    6 * ζ ^ 2 * y * z - 3 * ζ * x * y - 3 * ζ * x * z + 3 * ζ * y * z + 3 * x ^ 2 -
    3 * x * y - 3 * x * z + 3 * y * z) * hζ

/-- The paper's `√disc = (X-Z)(Y-X)(Z-Y)` on the original cover. -/
def coverSqrtDisc : CoverRing :=
  (coverCoordinate 0 - coverCoordinate 2) * (coverCoordinate 1 - coverCoordinate 0) *
    (coverCoordinate 2 - coverCoordinate 1)

theorem coverSqrtDisc_fixed : coverSqrtDisc ∈ quotientFixedRing := by
  constructor
  · change SplitLaurentGalois.conjugate conjugation coverSqrtDisc = coverSqrtDisc
    simp only [coverSqrtDisc, map_sub, map_mul, coverCoordinate_conjugation]
  · change twist (rootUnit zeta zeta_relation) coverSqrtDisc = coverSqrtDisc
    simp only [coverSqrtDisc, map_sub, map_mul, coverCoordinate_twist]
    norm_num
    rw [show (-1 : ZMod 3) = 2 by decide]
    ring

/-- The descended `√disc`, with both descent conditions proved. -/
def sqrtDisc : quotientFixedRing := ⟨coverSqrtDisc, coverSqrtDisc_fixed⟩

/-- `√-27 = 3√-3`, with the paper's square root `2ζ+1` of `-3`. -/
def sqrtNegTwentySeven : E := 3 * sqrtNegThree

theorem sqrtNegTwentySeven_sq : sqrtNegTwentySeven ^ 2 = -27 := by
  rw [sqrtNegTwentySeven, mul_pow, sqrtNegThree_sq]
  norm_num

theorem conjugation_sqrtNegTwentySeven :
    conjugation sqrtNegTwentySeven = -sqrtNegTwentySeven := by
  simp only [sqrtNegTwentySeven, sqrtNegThree, map_mul, map_add, map_one, map_ofNat,
    conjugation_zeta]
  ring

theorem sqrtNegTwentySeven_ne_zero : sqrtNegTwentySeven ≠ 0 := by
  intro h
  have := sqrtNegTwentySeven_sq
  rw [h] at this
  norm_num at this

/-- The characters `χ₁³ - χ₂³ = √-27 √disc` on the original cover. -/
theorem cover_cubes_difference :
    AddMonoidAlgebra.single (3, 0) (1 : E) - AddMonoidAlgebra.single (0, 3) 1 =
      algebraMap E CoverRing sqrtNegTwentySeven * coverSqrtDisc := by
  have h1 := universal_first_character
  have h2 := universal_second_character
  rw [firstCharacter, character_val] at h1
  rw [secondCharacter_val] at h2
  have hs : (AddMonoidAlgebra.single (3, 0) (1 : E) : CoverRing) =
      AddMonoidAlgebra.single (1, 0) (1 : E) ^ 3 := by
    rw [AddMonoidAlgebra.single_pow, one_pow]
    rfl
  have ht : (AddMonoidAlgebra.single (0, 3) (1 : E) : CoverRing) =
      AddMonoidAlgebra.single (0, 1) (1 : E) ^ 3 := by
    rw [AddMonoidAlgebra.single_pow, one_pow]
    rfl
  rw [hs, ht, ← h1, ← h2]
  change _ = algebraMap E CoverRing sqrtNegTwentySeven *
    ((coverCoordinate 0 - coverCoordinate 2) * (coverCoordinate 1 - coverCoordinate 0) *
      (coverCoordinate 2 - coverCoordinate 1))
  have hz : (algebraMap E CoverRing zeta) ^ 2 + algebraMap E CoverRing zeta + 1 = 0 :=
    root_relation zeta zeta_relation
  rw [eigenvalue_cubes_difference _ hz]
  simp only [sqrtNegTwentySeven, sqrtNegThree, map_mul, map_add, map_one, map_ofNat]
  rfl

/-- `√disc` in quotient Laurent coordinates. -/
def sqrtDiscExpression : CoverRing :=
  algebraMap E CoverRing sqrtNegTwentySeven⁻¹ *
    (AddMonoidAlgebra.single (2, 1) (1 : E) - AddMonoidAlgebra.single (1, 2) 1)

theorem sqrtDiscExpression_fixed :
    SplitLaurentGalois.conjugate conjugation sqrtDiscExpression = sqrtDiscExpression := by
  simp only [sqrtDiscExpression, map_mul, map_sub, SplitLaurentGalois.conjugate_algebraMap,
    SplitLaurentGalois.conjugate_single, map_one, Prod.swap_prod_mk, map_inv₀,
    conjugation_sqrtNegTwentySeven, inv_neg, map_neg]
  ring

theorem sqrtDiscExpression_pullback : pullbackHom sqrtDiscExpression = coverSqrtDisc := by
  simp only [sqrtDiscExpression, map_mul, map_sub, pullbackHom_single, AlgHom.commutes]
  change algebraMap E CoverRing sqrtNegTwentySeven⁻¹ *
    (AddMonoidAlgebra.single (3, 0) (1 : E) - AddMonoidAlgebra.single (0, 3) 1) = _
  rw [cover_cubes_difference, ← mul_assoc, ← map_mul, inv_mul_cancel₀ sqrtNegTwentySeven_ne_zero,
    map_one, one_mul]

theorem sqrtDisc_image : fixedRingEquiv ⟨sqrtDiscExpression, sqrtDiscExpression_fixed⟩ = sqrtDisc :=
  Subtype.ext sqrtDiscExpression_pullback

/-- `√disc² = disc` for the cubic `t³-t²+e₂t-e₃`, with `constantCoefficient = -e₃`. -/
theorem sqrtDisc_sq :
    sqrtDisc ^ 2 = linearCoefficient ^ 2 - 4 * linearCoefficient ^ 3 +
      4 * constantCoefficient - 27 * constantCoefficient ^ 2 -
        18 * linearCoefficient * constantCoefficient := by
  apply Subtype.ext
  change coverSqrtDisc ^ 2 = coverLinearCoefficient ^ 2 - 4 * coverLinearCoefficient ^ 3 +
    4 * coverConstantCoefficient - 27 * coverConstantCoefficient ^ 2 -
      18 * coverLinearCoefficient * coverConstantCoefficient
  have ht := trace_one CoverRing universalCover
  change coverCoordinate 0 + coverCoordinate 1 + coverCoordinate 2 = 1 at ht
  have hz : coverCoordinate 2 = 1 - coverCoordinate 0 - coverCoordinate 1 := by
    linear_combination ht
  simp only [coverSqrtDisc, coverLinearCoefficient, coverConstantCoefficient, secondCoeff,
    constantCoeff, hz]
  ring

section Local

variable (A : Type*) [CommRing A] [Algebra ℚ A]
variable {L : Type*} [Field L] [CharZero L]
variable (place : E ⊗[ℚ] A →+* L)

/-- The two conjugate weight-vector values at a point, after a place map. -/
def weightValue (sign : ℤ) (P : quotientFixedRing →ₐ[ℚ] A) : L :=
  place ((1 : E) ⊗ₜ[ℚ] (1 - (9 / 2 : ℚ) • P linearCoefficient -
    (27 / 2 : ℚ) • P constantCoefficient)) +
    (sign : L) / 2 * place (sqrtNegTwentySeven ⊗ₜ[ℚ] (1 : A)) *
      place ((1 : E) ⊗ₜ[ℚ] P sqrtDisc)

omit [CharZero L] in
private theorem value_monomial (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) :
    ((localCharacter A place P (Multiplicative.ofAdd m) : Lˣ) : L) =
      evaluation A place P (AddMonoidAlgebra.single m 1) := by
  rw [evaluation_monomial]
  simp [localCharacter, characterValues_formula]

omit [CharZero L] in
private theorem evaluation_scalar (P : quotientFixedRing →ₐ[ℚ] A) (x : E) :
    evaluation A place P (algebraMap E CoverRing x) = place (x ⊗ₜ[ℚ] (1 : A)) := by
  change place (extendPoint (quotientPresentation A P) (algebraMap E CoverRing x)) = _
  rw [AlgHom.commutes]
  rfl

omit [CharZero L] in
private theorem evaluation_sqrtDisc (P : quotientFixedRing →ₐ[ℚ] A) :
    evaluation A place P sqrtDiscExpression = place ((1 : E) ⊗ₜ[ℚ] P sqrtDisc) := by
  have h := evaluation_fixed A place P ⟨sqrtDiscExpression, sqrtDiscExpression_fixed⟩
  rwa [sqrtDisc_image] at h

omit [CharZero L] in
private theorem evaluation_linear (P : quotientFixedRing →ₐ[ℚ] A) :
    evaluation A place P linearExpression = place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient) := by
  have h := evaluation_fixed A place P ⟨linearExpression, linearExpression_fixed⟩
  rwa [show fixedRingEquiv ⟨linearExpression, linearExpression_fixed⟩ = linearCoefficient from
    Subtype.ext linearExpression_pullback] at h

omit [CharZero L] in
private theorem evaluation_constant (P : quotientFixedRing →ₐ[ℚ] A) :
    evaluation A place P constantExpression = place ((1 : E) ⊗ₜ[ℚ] P constantCoefficient) := by
  have h := evaluation_fixed A place P ⟨constantExpression, constantExpression_fixed⟩
  rwa [show fixedRingEquiv ⟨constantExpression, constantExpression_fixed⟩ = constantCoefficient from
    Subtype.ext constantExpression_pullback] at h

theorem place_tmul (P : quotientFixedRing →ₐ[ℚ] A) :
    place ((1 : E) ⊗ₜ[ℚ] (1 - (9 / 2 : ℚ) • P linearCoefficient -
      (27 / 2 : ℚ) • P constantCoefficient)) =
      1 - 9 / 2 * place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient) -
        27 / 2 * place ((1 : E) ⊗ₜ[ℚ] P constantCoefficient) := by
  simp only [TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_sub, map_rat_smul]
  rw [← Algebra.TensorProduct.one_def, map_one]
  simp only [Rat.smul_def]
  push_cast
  ring

/-- `eqn:formulaForNormCharacter2` and its conjugate, at every point after any place map. -/
theorem character_eq_weightValue (P : quotientFixedRing →ₐ[ℚ] A) :
    ((localCharacter A place P (Multiplicative.ofAdd (2, 1)) : Lˣ) : L) =
        weightValue A place 1 P ∧
      ((localCharacter A place P (Multiplicative.ofAdd (1, 2)) : Lˣ) : L) =
        weightValue A place (-1) P := by
  have hs := sqrtDiscExpression_fixed
  rw [weightValue, weightValue, place_tmul, ← evaluation_linear, ← evaluation_constant,
    ← evaluation_sqrtDisc, ← evaluation_scalar A place P, value_monomial, value_monomial]
  have hk : evaluation A place P (algebraMap E CoverRing sqrtNegTwentySeven) *
      evaluation A place P (algebraMap E CoverRing sqrtNegTwentySeven⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ sqrtNegTwentySeven_ne_zero, map_one, map_one]
  simp only [linearExpression, constantExpression, sqrtDiscExpression, Algebra.smul_def, map_mul,
    RingHom.map_rat_algebraMap, map_sub, map_one, map_ofNat, map_div₀]
  constructor
  · push_cast
    linear_combination (-1 / 2 * (evaluation A place P (AddMonoidAlgebra.single (2, 1) 1) -
      evaluation A place P (AddMonoidAlgebra.single (1, 2) 1))) * hk
  · push_cast
    linear_combination (1 / 2 * (evaluation A place P (AddMonoidAlgebra.single (2, 1) 1) -
      evaluation A place P (AddMonoidAlgebra.single (1, 2) 1))) * hk

/-- The norm-character weight vector is `1-3e₂`. -/
theorem normCharacter_value (P : quotientFixedRing →ₐ[ℚ] A) :
    ((localCharacter A place P (Multiplicative.ofAdd (1, 1)) : Lˣ) : L) =
      1 - 3 * place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient) := by
  rw [value_monomial, ← evaluation_linear]
  simp only [linearExpression, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap, map_sub,
    map_one, map_div₀, map_ofNat]
  ring

omit [CharZero L] in
/-- Base scalars followed by the place map. -/
def scalarPlace : A →+* L :=
  place.comp (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] E ⊗[ℚ] A).toRingHom

omit [CharZero L] in
theorem scalarPlace_apply (a : A) : scalarPlace A place a = place ((1 : E) ⊗ₜ[ℚ] a) := rfl

/-- The paper's short computation: `z₊ z₋ = (1-3e₂)³`, from `√disc² = disc`. -/
theorem weightValue_mul (P : quotientFixedRing →ₐ[ℚ] A) :
    weightValue A place 1 P * weightValue A place (-1) P =
      (1 - 3 * place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient)) ^ 3 := by
  have hd := congrArg (fun f : quotientFixedRing => scalarPlace A place (P f)) sqrtDisc_sq
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hd
  have hk : place (sqrtNegTwentySeven ⊗ₜ[ℚ] (1 : A)) ^ 2 = -27 := by
    change (place.comp (Algebra.TensorProduct.includeLeft : E →ₐ[ℚ] E ⊗[ℚ] A).toRingHom)
      sqrtNegTwentySeven ^ 2 = -27
    rw [← map_pow, sqrtNegTwentySeven_sq, map_neg, map_ofNat]
  rw [weightValue, weightValue, place_tmul]
  simp only [← scalarPlace_apply] at hd ⊢
  push_cast
  linear_combination ((27 / 4 : L)) * hd + (-(1 / 4 : L)) *
    scalarPlace A place (P sqrtDisc) ^ 2 * hk

end Local

end Cubic.ToricHeights.WeightVectors
