import Cubic.QuadraticCorrespondence.RationalQuotientFunctor
import Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-!
# Descending the original characteristic-polynomial coefficients

The universal point of the original augmentation-one cover supplies three
coordinate functions. We form their elementary symmetric functions first,
then prove their Laurent expressions and descent to the rational cyclic
invariant ring. The norm/trace formulas for these coefficients are therefore
theorems rather than definitions.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.DescendedCoefficients

open scoped Polynomial TensorProduct
open CyclotomicField CyclotomicTorusGalois
open SplitLaurentInvariants SplitLaurentPoints SplitCoverFunctor
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters

abbrev CoverRing := LaurentRing (K := E)

/-- The universal point is obtained from the representation of the original cover. -/
def universalCover : traceOneUnits CoverRing :=
  (coverPointEquiv zeta zeta_relation).symm (AlgHom.id E CoverRing)

/-- The original three group-algebra coefficients as universal regular functions. -/
def coverCoordinate (i : ZMod 3) : CoverRing := (universalCover.val : GroupAlgebra CoverRing) i

/-- The original elementary symmetric function `e₂`. -/
def coverLinearCoefficient : CoverRing :=
  secondCoeff (coverCoordinate 0) (coverCoordinate 1) (coverCoordinate 2)

/-- The original negative third elementary symmetric function `-e₃`. -/
def coverConstantCoefficient : CoverRing :=
  constantCoeff (coverCoordinate 0) (coverCoordinate 1) (coverCoordinate 2)

theorem universal_characters :
    charactersOverAlgebra zeta zeta_relation universalCover =
      (monomialUnit (K := E) (Multiplicative.ofAdd (1, 0)),
        monomialUnit (K := E) (Multiplicative.ofAdd (0, 1))) := by
  have h := congrArg SplitLaurentPoints.coordinates
    ((coverPointEquiv zeta zeta_relation).apply_symm_apply (AlgHom.id E CoverRing))
  simpa only [universalCover, coverPointEquiv_apply, coordinates_evaluate] using h

theorem universal_first_character :
    (firstCharacter (algebraMap E CoverRing zeta) (root_relation zeta zeta_relation) universalCover :
      CoverRing) = AddMonoidAlgebra.single (1, 0) (1 : E) :=
  congrArg (fun x : CoverRingˣ × CoverRingˣ => (x.1 : CoverRing)) universal_characters

theorem universal_second_character :
    (secondCharacter (algebraMap E CoverRing zeta) (root_relation zeta zeta_relation) universalCover :
      CoverRing) = AddMonoidAlgebra.single (0, 1) (1 : E) :=
  congrArg (fun x : CoverRingˣ × CoverRingˣ => (x.2 : CoverRing)) universal_characters

/-- Evaluation of the universal point gives the original point, including its coefficients. -/
theorem map_universal {R : Type*} [CommRing R] [Algebra E R] (g : traceOneUnits R) :
    mapUnits (coverPointEquiv zeta zeta_relation g).toRingHom universalCover = g := by
  apply (coverPointEquiv zeta zeta_relation).injective
  rw [coverPointEquiv_mapUnits]
  have h : coverPointEquiv zeta zeta_relation universalCover = AlgHom.id E CoverRing :=
    (coverPointEquiv zeta zeta_relation).apply_symm_apply _
  rw [h, AlgHom.comp_id]

theorem evaluate_coverCoordinate {R : Type*} [CommRing R] [Algebra E R]
    (g : traceOneUnits R) (i : ZMod 3) :
    coverPointEquiv zeta zeta_relation g (coverCoordinate i) = (g.val : GroupAlgebra R) i := by
  exact congrArg (fun h : traceOneUnits R => (h.val : GroupAlgebra R) i) (map_universal g)

theorem evaluate_coverLinearCoefficient {R : Type*} [CommRing R] [Algebra E R]
    (g : traceOneUnits R) :
    coverPointEquiv zeta zeta_relation g coverLinearCoefficient =
      secondCoeff ((g.val : GroupAlgebra R) 0) ((g.val : GroupAlgebra R) 1)
        ((g.val : GroupAlgebra R) 2) := by
  simp only [coverLinearCoefficient, secondCoeff, map_add, map_mul, evaluate_coverCoordinate]

theorem evaluate_coverConstantCoefficient {R : Type*} [CommRing R] [Algebra E R]
    (g : traceOneUnits R) :
    coverPointEquiv zeta zeta_relation g coverConstantCoefficient =
      constantCoeff ((g.val : GroupAlgebra R) 0) ((g.val : GroupAlgebra R) 1)
        ((g.val : GroupAlgebra R) 2) := by
  simp only [coverConstantCoefficient, constantCoeff, map_neg, map_mul, evaluate_coverCoordinate]

/-- The expression in quotient Laurent coordinates, before its geometric identification. -/
def linearExpression : CoverRing :=
  (1 / 3 : ℚ) • (1 - AddMonoidAlgebra.single (1, 1) (1 : E))

/-- The expression uses the exact monomials `N` and `NT` of the paper. -/
def constantExpression : CoverRing :=
  (1 / 27 : ℚ) • (3 * AddMonoidAlgebra.single (1, 1) (1 : E) -
    AddMonoidAlgebra.single (2, 1) 1 - AddMonoidAlgebra.single (1, 2) 1 - 1)

private theorem norm_identity :
    AddMonoidAlgebra.single (1, 1) (1 : E) = 1 - 3 * coverLinearCoefficient := by
  have h := character_product (algebraMap E CoverRing zeta)
    (root_relation zeta zeta_relation) universalCover
  rw [universal_first_character, universal_second_character] at h
  simpa only [AddMonoidAlgebra.single_mul_single, one_mul] using h

private theorem cube_sum_identity :
    AddMonoidAlgebra.single (3, 0) (1 : E) + AddMonoidAlgebra.single (0, 3) 1 =
      2 - 9 * coverLinearCoefficient - 27 * coverConstantCoefficient := by
  have h := character_cubes_sum (algebraMap E CoverRing zeta)
    (root_relation zeta zeta_relation) universalCover
  rw [universal_first_character, universal_second_character] at h
  simpa only [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, Prod.smul_mk,
    smul_zero, smul_eq_mul, mul_one] using h

/-- The quotient-character formula equals the original coefficient. -/
theorem linearExpression_pullback : pullbackHom linearExpression = coverLinearCoefficient := by
  have h : (3 : ℚ) • coverLinearCoefficient =
      1 - AddMonoidAlgebra.single (1, 1) (1 : E) := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination norm_identity
  simp only [linearExpression, map_rat_smul, map_sub, map_one, pullbackHom_single]
  change (1 / 3 : ℚ) • (1 - AddMonoidAlgebra.single (1, 1) (1 : E)) = _
  rw [← h, smul_smul]
  norm_num

theorem constantExpression_pullback : pullbackHom constantExpression = coverConstantCoefficient := by
  have h : (27 : ℚ) • coverConstantCoefficient =
      3 * AddMonoidAlgebra.single (1, 1) (1 : E) -
        AddMonoidAlgebra.single (3, 0) 1 - AddMonoidAlgebra.single (0, 3) 1 - 1 := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination cube_sum_identity - 3 * norm_identity
  simp only [constantExpression, map_rat_smul, map_sub, map_mul, map_ofNat, map_one,
    pullbackHom_single]
  change (1 / 27 : ℚ) • (3 * AddMonoidAlgebra.single (1, 1) (1 : E) -
    AddMonoidAlgebra.single (3, 0) 1 - AddMonoidAlgebra.single (0, 3) 1 - 1) = _
  rw [← h, smul_smul]
  norm_num

theorem linearExpression_fixed :
    SplitLaurentGalois.conjugate conjugation linearExpression = linearExpression := by
  simp [linearExpression, map_smul, SplitLaurentGalois.conjugate_single]

theorem constantExpression_fixed :
    SplitLaurentGalois.conjugate conjugation constantExpression = constantExpression := by
  simp only [constantExpression, map_smul, map_sub, map_mul, map_ofNat, map_one,
    SplitLaurentGalois.conjugate_single, Prod.swap_prod_mk]
  congr 1
  abel

private theorem linear_mem_quotient : coverLinearCoefficient ∈ quotientFixedRing := by
  rw [← linearExpression_pullback]
  exact (fixedRingEquiv ⟨linearExpression, linearExpression_fixed⟩).property

private theorem constant_mem_quotient : coverConstantCoefficient ∈ quotientFixedRing := by
  rw [← constantExpression_pullback]
  exact (fixedRingEquiv ⟨constantExpression, constantExpression_fixed⟩).property

/-- The original linear coefficient, which descends to the rational quotient ring. -/
def linearCoefficient : quotientFixedRing := ⟨coverLinearCoefficient, linear_mem_quotient⟩

/-- The constant coefficient descends with its original characteristic-polynomial sign. -/
def constantCoefficient : quotientFixedRing := ⟨coverConstantCoefficient, constant_mem_quotient⟩

/-- The descended cubic is defined from the original symmetric coefficient functions. -/
def characteristicPolynomial (p : quotientFixedRing →ₐ[ℚ] ℚ) : ℚ[X] :=
  CorrespondencePolynomials.cubic (p linearCoefficient) (p constantCoefficient)

/-- On every rational coefficient algebra, the descended linear coefficient pulls
back to the original second elementary symmetric function. -/
theorem quotientPoint_linearCoefficient {A : Type*} [CommRing A] [Algebra ℚ A]
    (g : traceOneUnits A) :
    RationalQuotientFunctor.quotientPoint A g linearCoefficient =
      secondCoeff ((g.val : GroupAlgebra A) 0) ((g.val : GroupAlgebra A) 1)
        ((g.val : GroupAlgebra A) 2) := by
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] RationalQuotientFunctor.quotientPoint A g linearCoefficient = _
  rw [RationalQuotientFunctor.quotientPoint_baseChange]
  change coverPointEquiv zeta zeta_relation (CyclotomicCoverDescent.extendCover A g)
    coverLinearCoefficient = _
  rw [evaluate_coverLinearCoefficient]
  simp only [secondCoeff, CyclotomicCoverDescent.extendCover, mapUnits_coefficient,
    map_add, map_mul]
  rfl

theorem quotientPoint_constantCoefficient {A : Type*} [CommRing A] [Algebra ℚ A]
    (g : traceOneUnits A) :
    RationalQuotientFunctor.quotientPoint A g constantCoefficient =
      constantCoeff ((g.val : GroupAlgebra A) 0) ((g.val : GroupAlgebra A) 1)
        ((g.val : GroupAlgebra A) 2) := by
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] RationalQuotientFunctor.quotientPoint A g constantCoefficient = _
  rw [RationalQuotientFunctor.quotientPoint_baseChange]
  change coverPointEquiv zeta zeta_relation (CyclotomicCoverDescent.extendCover A g)
    coverConstantCoefficient = _
  rw [evaluate_coverConstantCoefficient]
  simp only [constantCoeff, CyclotomicCoverDescent.extendCover, mapUnits_coefficient,
    map_neg, map_mul]
  rfl

end Cubic.QuadraticCorrespondence.DescendedCoefficients
