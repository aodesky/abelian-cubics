import Cubic.ToricHeights.IntegralPolynomialData
import Cubic.ToricHeights.RootHeightDiscriminant
import Cubic.PoissonSummation.IntegralPointComparison
import Cubic.ToricHeights.CanonicalHeight
import Cubic.QuadraticCorrespondence.RationalCorrespondence

/-!
# Coefficients, discriminant and height on integral quotient points

The height identity is `prop:canonicalHeight`, proved along the paper's
weight-vector route. `discriminant_square` gives the discriminant inequality from the
norm/trace formulas; it is used only by the alternative proof
`RootVsToric.claim_via_discriminant_square`. The labelled `lemma:rootVsToric`
uses the paper's real-root route (`IntegralPolynomialRealRoots.discriminant_nonneg`).
-/

noncomputable section

namespace Cubic.ToricHeights.IntegralPolynomialHeight

open IntegralPolynomialData Cubic.PoissonSummation Cubic.QuadraticCorrespondence
open DescendedCoefficients RationalCoefficientFormula CyclotomicField
open Polynomial

theorem linear_cast (P : Points) : (linear P : ℚ) = P.val linearCoefficient := by
  obtain ⟨⟨a, ha⟩, _⟩ := (IntegralPointComparison.coefficient_criterion P.val).mp P.property
  simp [linear, ha]

theorem constant_cast (P : Points) : (constant P : ℚ) = P.val constantCoefficient := by
  obtain ⟨_, ⟨b, hb⟩⟩ := (IntegralPointComparison.coefficient_criterion P.val).mp P.property
  simp [constant, hb]

theorem polynomial_descended (P : Points) :
    (polynomial P).map (Int.castRingHom ℚ) = characteristicPolynomial P.val := by
  simp [polynomial, Counting.PolynomialCountData.traceOneCubic, characteristicPolynomial,
    CorrespondencePolynomials.cubic, ← linear_cast P, ← constant_cast P]

/-- `prop:canonicalHeight` gives `H(f)² = 1-3a > 0`, as in the paper's proof of `lemma:rootVsToric`. -/
theorem coefficient_height_positive (P : Points) : 0 < 1 - 3 * (linear P : ℝ) := by
  have h := CanonicalHeight.norm_ge_one P.val P.property
  rw [show (linear P : ℝ) = ((P.val linearCoefficient : ℚ) : ℝ) by exact_mod_cast linear_cast P]
  linarith

theorem linear_nonpos (P : Points) : linear P ≤ 0 := by
  have hz : (0 : ℤ) < 1 - 3 * linear P := by
    exact_mod_cast coefficient_height_positive P
  omega

theorem height_eq_sqrt (P : Points) :
    AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal P.val) =
      (Real.sqrt (1 - 3 * (linear P : ℝ)) : ℂ) := by
  rw [CanonicalHeight.«prop:canonicalHeight».2 P.val P.property,
    show (linear P : ℝ) = ((P.val linearCoefficient : ℚ) : ℝ) by exact_mod_cast linear_cast P]

theorem toricHeight_eq_sqrt (P : Points) :
    toricHeight P = Real.sqrt (1 - 3 * (linear P : ℝ)) := by
  simpa only [toricHeight, Complex.ofReal_re] using congrArg Complex.re (height_eq_sqrt P)

theorem height_real (P : Points) :
    AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal P.val) =
      (toricHeight P : ℂ) := by
  rw [toricHeight_eq_sqrt, height_eq_sqrt]

theorem toricHeight_nonneg (P : Points) : 0 ≤ toricHeight P := by
  rw [toricHeight_eq_sqrt]
  exact Real.sqrt_nonneg _

theorem toricHeight_square (P : Points) : toricHeight P ^ 2 = 1 - 3 * (linear P : ℝ) := by
  rw [toricHeight_eq_sqrt, Real.sq_sqrt (coefficient_height_positive P).le]

/-- The cubic discriminant is the square `(N v / 3)^2` in cyclotomic coordinates. -/
theorem discriminant_square (P : AdelicHeightZetaData.RationalPoints) :
    IsSquare (⟨1, -1, P linearCoefficient, P constantCoefficient⟩ : Cubic ℚ).discr := by
  obtain ⟨u, v, huv⟩ := exists_linear (parameterEquiv P : E)
  rw [linearCoefficient_eq, constantCoefficient_eq, huv, norm_linear, trace_linear]
  refine ⟨CyclotomicCoefficients.normForm u v * v / 3, ?_⟩
  simp only [Cubic.discr, CyclotomicCoefficients.normForm, CyclotomicCoefficients.traceForm]
  ring

theorem discriminant_nonneg (P : Points) :
    0 ≤ (linear P : ℝ) ^ 2 - 4 * (linear P : ℝ) ^ 3 +
      (4 - 18 * (linear P : ℝ)) * constant P - 27 * (constant P : ℝ) ^ 2 := by
  have h := (discriminant_square P.val).nonneg
  simp only [Cubic.discr] at h
  rw [← linear_cast P, ← constant_cast P] at h
  have hq : (0 : ℚ) ≤ (linear P : ℚ) ^ 2 - 4 * (linear P : ℚ) ^ 3 +
      (4 - 18 * (linear P : ℚ)) * constant P - 27 * (constant P : ℚ) ^ 2 := by
    nlinarith [h]
  exact_mod_cast hq

theorem rootHeight_eq_sqrt (P : Points) : rootHeight P = Real.sqrt (-(linear P : ℝ)) :=
  RootHeightDiscriminant.rootHeight_eq_sqrt _ _ (linear_nonpos P) (discriminant_nonneg P)

end Cubic.ToricHeights.IntegralPolynomialHeight
