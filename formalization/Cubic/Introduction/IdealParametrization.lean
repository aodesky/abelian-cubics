import CubicTargets.Introduction.IdealParametrization
import Cubic.Introduction.IntegralIdeals
import Cubic.Introduction.ResolventCubes
import Cubic.PoissonSummation.IntegralHeightNormalization
import Cubic.PoissonSummation.HeightZetaFullRegion

noncomputable section

namespace Cubic.Introduction.IdealParametrization

open EisensteinPointData IntegralEisenstein IntegralIdeals
open Cubic.QuadraticCorrespondence CyclotomicField RationalCoefficientFormula
open QuotientPolynomialFibres DescendedCoefficients
open CorrespondencePolynomials

theorem resolvent_conjugate (α : E) :
    EisensteinPointData.resolvent (conjugation α) =
      conjugation (EisensteinPointData.resolvent α) := by
  simp only [EisensteinPointData.resolvent, norm_eq_mul_conjugation, map_mul]

theorem polynomial_fibres (P Q : IntegralTorus) :
    characteristicPolynomial P.1 = characteristicPolynomial Q.1 ↔
    pointResolvent Q.1 = pointResolvent P.1 ∨
      pointResolvent Q.1 = conjugation (pointResolvent P.1) := by
  rw [eq_comm, polynomial_eq_iff]
  have hi : Function.Injective pointResolvent := by
    intro P Q h
    exact parameterEquiv.injective (Units.ext (resolvent_injective h))
  have hc : pointResolvent (conjugatePoint P.1) = conjugation (pointResolvent P.1) := by
    rw [pointResolvent, parameter_conjugate, resolvent_conjugate]
    rfl
  rw [← hc]
  exact or_congr hi.eq_iff.symm hi.eq_iff.symm

def pointIdealEquiv : IntegralTorus ≃ CubeIdeals := pointEquiv.trans idealEquiv

theorem ideal_norm_height (P : IntegralTorus) :
    (Ideal.absNorm (pointIdealEquiv P).1 : ℝ) = pointHeight P ^ 6 := by
  have h := norm_span (pointEquiv P).1
  have h' := norm_height P
  change (Ideal.absNorm (Ideal.span {(pointEquiv P).1}) : ℝ) = _
  exact (by exact_mod_cast h : (Ideal.absNorm (Ideal.span {(pointEquiv P).1}) : ℝ) =
    (Algebra.norm ℚ ((pointEquiv P).1 : E) : ℝ)).trans h'

theorem ideal_term (s : ℂ) (P : IntegralTorus) :
    (pointHeight P : ℂ) ^ (-s) =
      (Ideal.absNorm (pointIdealEquiv P).1 : ℂ) ^ (-s / 6) := by
  have hH : 0 ≤ pointHeight P := by
    simp only [pointHeight, Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight».2 P.1 P.2,
      Complex.ofReal_re]
    exact Real.sqrt_nonneg _
  have hN : (Ideal.absNorm (pointIdealEquiv P).1 : ℂ) = (pointHeight P : ℂ) ^ 6 := by
    exact_mod_cast ideal_norm_height P
  rw [hN, ← Complex.cpow_nat_mul']
  · congr 1
    ring
  · simp only [Complex.arg_ofReal_of_nonneg hH, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  · simp only [Complex.arg_ofReal_of_nonneg hH, mul_zero]
    exact Real.pi_pos.le

theorem series (s : ℂ) :
    (∑' P : IntegralTorus, (pointHeight P : ℂ) ^ (-s)) =
      ∑' J : CubeIdeals, (Ideal.absNorm J.1 : ℂ) ^ (-s / 6) := by
  rw [← pointIdealEquiv.tsum_eq]
  exact tsum_congr (ideal_term s)

theorem polynomial_image (a b : ℤ)
    (hc : CorrespondencePolynomials.HasCyclicCubicGaloisGroup
      (CorrespondencePolynomials.cubic a b)) :
    ∃ P : IntegralTorus, characteristicPolynomial P.1 =
      CorrespondencePolynomials.cubic a b := by
  obtain ⟨P, hP⟩ := QuotientPolynomialConverse.exists_point ⟨Or.inl hc, by
    rintro ⟨r, hr⟩
    apply Cubic.Counting.CyclicCubicField.not_isRoot_of_cyclic a b hc r
    simp [Polynomial.IsRoot, hr]⟩
  have ha : P linearCoefficient = a := by
    have h := congrArg (fun f : Polynomial ℚ => f.coeff 1) hP
    simpa only [characteristicPolynomial, cubic_coeff_one] using h
  have hb : P constantCoefficient = b := by
    have h := congrArg (fun f : Polynomial ℚ => f.coeff 0) hP
    simpa only [characteristicPolynomial, cubic_coeff_zero] using h
  exact ⟨⟨P, (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P).mpr
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩, hP⟩

open Cubic.PoissonSummation in
theorem point_term (s : ℂ) (P : IntegralTorus) :
    (pointHeight P : ℂ) ^ (-s) =
      AdelicHeightZetaData.zetaTerm s 0 (IntegralPointComparison.integralPointsEquiv P) := by
  let Q := IntegralPointComparison.integralPointsEquiv P
  let u := Cubic.ToricHeights.ArchimedeanQuotientLogarithm.coordinate
    (RationalAdelicEmbedding.baseChange ℝ Q.1)
  have hH : pointHeight P = Real.exp u := by
    change (AdelicHeightZetaData.height 1 0
      (RationalAdelicEmbedding.diagonal Q.1)).re = _
    rw [IntegralHeightNormalization.height_eq_exp Q 1]
    simp only [one_mul, ← Complex.ofReal_exp, Complex.ofReal_re]
    rfl
  change _ = (AdelicHeightZetaData.height s 0
    (RationalAdelicEmbedding.diagonal Q.1))⁻¹
  rw [hH, IntegralHeightNormalization.height_eq_exp Q s,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, ← Complex.exp_neg]
  congr 1
  dsimp [u]
  ring

open Cubic.PoissonSummation in
theorem point_absolute (s : ℂ) (hs : 2 < s.re) :
    Summable (fun P : IntegralTorus => ‖(pointHeight P : ℂ) ^ (-s)‖) := by
  simp_rw [point_term]
  exact IntegralPointComparison.integralPointsEquiv.summable_iff.mpr
    (HeightZetaFullRegion.series_absolute s 0 (by simpa using hs))

theorem ideal_absolute (s : ℂ) (hs : 2 < s.re) :
    Summable (fun J : CubeIdeals => ‖(Ideal.absNorm J.1 : ℂ) ^ (-s / 6)‖) := by
  apply pointIdealEquiv.summable_iff.mp
  change Summable (fun P : IntegralTorus =>
    ‖(Ideal.absNorm (pointIdealEquiv P).1 : ℂ) ^ (-s / 6)‖)
  simpa only [← ideal_term] using point_absolute s hs

theorem arithmetic_claim :
    CubicTargets.Introduction.IdealParametrization.Claim where
  parametrization := ⟨pointEquiv, toPrimary_val, norm_height, fun P => by
    rw [show ((pointEquiv P).1 : E) = pointResolvent P.1 from toPrimary_val P]
    exact ResolventCubes.cyclic_iff_nonCube P.1⟩
  fullAffine := ⟨affineEquiv.symm, fun P => by
    have h := congrArg Subtype.val (affineEquiv.apply_symm_apply P)
    exact h⟩
  ideals := ⟨idealEquiv, fun _ => rfl⟩
  idealCondition := ideal_condition
  polynomialFibres := polynomial_fibres
  polynomialImage := polynomial_image
  pointSeries_absolute := point_absolute
  idealSeries_absolute := ideal_absolute
  series s _ := series s

end Cubic.Introduction.IdealParametrization
