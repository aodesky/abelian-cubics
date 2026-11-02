import Cubic.ToricHeights.AffineIntegrality
import Cubic.QuadraticCorrespondence.RationalCoefficientFormula

/-! The oriented invariant `δ` determines the quadratic torus parameter.
This calculation supplies the affine-chart comparison without a scheme wrapper. -/

noncomputable section

namespace Cubic.ToricHeights.AffinePointParameter

open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open DescendedCoefficients SplitLaurentInvariants RationalCoefficientFormula
open DescendedCyclicInvariant Cubic.OrbitParametrization

theorem sqrt_ne_zero : sqrtNegThree ≠ 0 := by
  intro h
  have hs := sqrtNegThree_sq
  rw [h] at hs
  norm_num at hs

theorem conjugation_sqrt : conjugation sqrtNegThree = -sqrtNegThree := by
  simp only [sqrtNegThree, map_add, map_mul, map_one, map_ofNat, conjugation_zeta]
  ring

theorem eigenvalue_delta {R : Type*} [CommRing R] (ζ x y z : R)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (x + y * ζ + z * ζ ^ 2) ^ 3 - (x + y * ζ ^ 2 + z * ζ) ^ 3 =
      3 * (2 * ζ + 1) *
        (2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) -
          (x + y + z) * secondCoeff x y z - 3 * constantCoeff x y z) := by
  have hsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  have hc := TraceOneCharacters.root_cube ζ hζ
  unfold secondCoeff constantCoeff
  rw [hsq]
  ring_nf
  simp only [hc, hsq]
  ring

theorem delta_character_identity :
    AddMonoidAlgebra.single (3, 0) (1 : E) - AddMonoidAlgebra.single (0, 3) 1 =
      3 * algebraMap E CoverRing sqrtNegThree *
        (2 * coverDelta - coverLinearCoefficient - 3 * coverConstantCoefficient) := by
  have h := eigenvalue_delta (algebraMap E CoverRing zeta)
    (coverCoordinate 0) (coverCoordinate 1) (coverCoordinate 2)
    (SplitCoverFunctor.root_relation zeta zeta_relation)
  have ht := Cubic.OrbitParametrization.CyclicGroupAlgebra.trace_one CoverRing universalCover
  change coverCoordinate 0 + coverCoordinate 1 + coverCoordinate 2 = 1 at ht
  have h₁ := universal_first_character
  have h₂ := universal_second_character
  rw [TraceOneCharacters.firstCharacter,
    Cubic.OrbitParametrization.CyclicGroupAlgebra.character_val] at h₁
  rw [TraceOneCharacters.secondCharacter_val] at h₂
  change coverCoordinate 0 + coverCoordinate 1 * algebraMap E CoverRing zeta +
    coverCoordinate 2 * algebraMap E CoverRing zeta ^ 2 = _ at h₁
  change coverCoordinate 0 + coverCoordinate 1 * algebraMap E CoverRing zeta ^ 2 +
    coverCoordinate 2 * algebraMap E CoverRing zeta = _ at h₂
  rw [h₁, h₂, ht] at h
  simpa only [coverDelta, coverLinearCoefficient, coverConstantCoefficient, one_mul,
    sqrtNegThree, map_add, map_mul, map_ofNat, map_one,
    AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul,
    Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using h

def deltaExpression : CoverRing :=
  (1 / 2 : ℚ) • (linearExpression + 3 * constantExpression) +
    ((6 * sqrtNegThree)⁻¹ : E) •
      (AddMonoidAlgebra.single (2, 1) 1 - AddMonoidAlgebra.single (1, 2) 1)

theorem deltaExpression_pullback : pullbackHom deltaExpression = coverDelta := by
  have h := delta_character_identity
  simp only [deltaExpression, map_add, map_rat_smul, map_smul]
  simp only [map_mul, map_ofNat, linearExpression_pullback,
    constantExpression_pullback, map_sub, pullbackHom_single, CharacterLattice.pullback,
    Algebra.smul_def]
  change algebraMap ℚ CoverRing (1 / 2) *
      (coverLinearCoefficient + 3 * coverConstantCoefficient) +
    algebraMap E CoverRing ((6 * sqrtNegThree)⁻¹) *
      (AddMonoidAlgebra.single (3, 0) 1 - AddMonoidAlgebra.single (0, 3) 1) = _
  rw [h]
  have hhalf : algebraMap ℚ CoverRing (1 / 2) = algebraMap E CoverRing (1 / 2) := by
    simp
  rw [hhalf]
  have htwo : algebraMap E CoverRing (1 / 2) * (2 : CoverRing) = 1 := by
    rw [← map_ofNat (algebraMap E CoverRing) 2, ← map_mul]
    norm_num
    rfl
  have hm : (6 * sqrtNegThree)⁻¹ * (3 * sqrtNegThree) = (1 / 2 : E) := by
    field_simp [sqrt_ne_zero]
    ring
  have hm' := congrArg (algebraMap E CoverRing) hm
  simp only [map_mul, map_ofNat] at hm'
  rw [← mul_assoc, hm']
  linear_combination coverDelta * htwo

theorem deltaExpression_inverse :
    ((fixedRingEquiv.symm delta : coverFixedRing) : CoverRing) = deltaExpression := by
  apply pullbackHom_injective
  have h := congrArg Subtype.val (fixedRingEquiv.apply_symm_apply delta)
  change pullbackHom ((fixedRingEquiv.symm delta : coverFixedRing) : CoverRing) = coverDelta at h
  exact h.trans deltaExpression_pullback.symm

theorem delta_formula (P : quotientFixedRing →ₐ[ℚ] ℚ) :
    algebraMap ℚ E (P delta) =
      (algebraMap ℚ E (P linearCoefficient) + 3 * algebraMap ℚ E (P constantCoefficient)) / 2 +
      ((parameterEquiv P : E) ^ 2 * conjugation (parameterEquiv P : E) -
        (parameterEquiv P : E) * conjugation (parameterEquiv P : E) ^ 2) /
          (6 * sqrtNegThree) := by
  have hd := splitEvaluation_fixed P (fixedRingEquiv.symm delta)
  rw [fixedRingEquiv.apply_symm_apply, deltaExpression_inverse] at hd
  have ha := splitEvaluation_fixed P ⟨linearExpression, linearExpression_fixed⟩
  rw [linearExpression_image] at ha
  have hb := splitEvaluation_fixed P ⟨constantExpression, constantExpression_fixed⟩
  rw [constantExpression_image] at hb
  rw [← hd]
  simp only [deltaExpression, map_add, map_rat_smul, map_smul]
  rw [map_mul, map_ofNat, ha, hb, map_sub,
    splitEvaluation_monomial, splitEvaluation_monomial]
  simp only [zpow_ofNat, Algebra.smul_def, Algebra.algebraMap_self_apply,
    map_div₀, map_one, map_ofNat]
  ring

theorem parameter_equation (P : quotientFixedRing →ₐ[ℚ] ℚ) :
    2 * (1 - 3 * algebraMap ℚ E (P linearCoefficient)) * (parameterEquiv P : E) =
      2 - 9 * algebraMap ℚ E (P linearCoefficient) -
        27 * algebraMap ℚ E (P constantCoefficient) +
      3 * sqrtNegThree * (2 * algebraMap ℚ E (P delta) -
        algebraMap ℚ E (P linearCoefficient) - 3 * algebraMap ℚ E (P constantCoefficient)) := by
  have ha := congrArg (algebraMap ℚ E) (linearCoefficient_eq P)
  simp only [map_div₀, map_sub, map_one, map_ofNat, norm_eq_mul_conjugation] at ha
  have hb := congrArg (algebraMap ℚ E) (constantCoefficient_eq P)
  simp only [map_div₀, map_sub, map_one, map_ofNat, map_mul,
    norm_eq_mul_conjugation, trace_eq_add_conjugation] at hb
  have hd := delta_formula P
  field_simp [sqrt_ne_zero] at ha hb hd
  linear_combination (-2 * (parameterEquiv P : E) + 3) * ha + hb - hd / 2

end Cubic.ToricHeights.AffinePointParameter
