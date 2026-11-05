import Cubic.ToricHeights.IntegralPolynomialRealRoots
import CubicTargets.ToricHeights.RootVsToric

/-!
# Root height and toric height

Following the paper, the split/cyclic classification of the descended cubic
and complex conjugation give three real roots. Comparing coefficients and
applying AM–GM to their squares bounds `b` (`IntegralPolynomialRealRoots`,
`RootHeightAMGM`); substituting `h(f)² = -a` into `H(f)² = 1 - 3a` gives the
remaining assertions.
-/

noncomputable section

namespace Cubic.ToricHeights.RootVsToric

open IntegralPolynomialData IntegralPolynomialHeight Polynomial

private theorem root_formula (P : Points) : rootHeight P = Real.sqrt (-(linear P : ℝ)) :=
  RootHeightAMGM.rootHeight_eq_sqrt _ _ (linear_nonpos P)
    (IntegralPolynomialRealRoots.constant_sq_le P)

theorem root_nonneg (P : Points) : 0 ≤ rootHeight P := by
  rw [root_formula]
  exact Real.sqrt_nonneg _

theorem root_square (P : Points) : rootHeight P ^ 2 = -(linear P : ℝ) := by
  rw [root_formula, Real.sq_sqrt]
  exact_mod_cast neg_nonneg.mpr (linear_nonpos P)

theorem toric_square (P : Points) : toricHeight P ^ 2 = 1 + 3 * rootHeight P ^ 2 := by
  rw [toricHeight_square, root_square]
  ring

theorem bounds (P : Points) (B : ℝ) (hB : 0 ≤ B) :
    rootHeight P ≤ B ↔ toricHeight P ≤ Real.sqrt (1 + 3 * B ^ 2) := by
  rw [← sq_le_sq₀ (root_nonneg P) hB,
    ← sq_le_sq₀ (toricHeight_nonneg P) (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : 0 ≤ 1 + 3 * B ^ 2), toric_square]
  constructor <;> intro h <;> linarith

theorem comparison (P : Points) : max 1 (rootHeight P) ≤ toricHeight P ∧
    toricHeight P ≤ 2 * max 1 (rootHeight P) := by
  have hH := toricHeight_nonneg P
  have hh := root_nonneg P
  have hs := toric_square P
  have hm : 1 ≤ max 1 (rootHeight P) := le_max_left _ _
  have hhm : rootHeight P ^ 2 ≤ (max 1 (rootHeight P)) ^ 2 :=
    (sq_le_sq₀ hh (by positivity)).mpr (le_max_right _ _)
  constructor
  · apply max_le <;> nlinarith [sq_nonneg (rootHeight P)]
  · nlinarith [sq_nonneg (max 1 (rootHeight P) - 1)]

theorem zero_iff (P : Points) : rootHeight P = 0 ↔ polynomial P = X ^ 3 - X ^ 2 := by
  constructor
  · intro h
    have ha : linear P = 0 := by
      have := root_square P
      rw [h] at this
      have : (linear P : ℝ) = 0 := by nlinarith
      exact_mod_cast this
    have hb : constant P = 0 := by
      apply RootHeightAMGM.zero_constant
      simpa only [ha, Int.cast_zero] using IntegralPolynomialRealRoots.constant_sq_le P
    simp [polynomial, Counting.PolynomialCountData.traceOneCubic, ha, hb]
  · intro h
    change Counting.PolynomialCountData.rootHeight (polynomial P) = 0
    rw [h]
    simp [Counting.PolynomialCountData.rootHeight]

theorem zero_height (P : Points) (h : rootHeight P = 0) : toricHeight P = 1 := by
  have hs := toric_square P
  rw [h] at hs
  nlinarith [toricHeight_nonneg P]

end Cubic.ToricHeights.RootVsToric

/-- The full height-comparison lemma, following the paper's AM–GM proof. -/
theorem Cubic.ToricHeights.«lemma:rootVsToric» : CubicTargets.ToricHeights.RootVsToric.Claim := by
  intro P
  exact {
    descended := IntegralPolynomialHeight.polynomial_descended P
    height_real := IntegralPolynomialHeight.height_real P
    linear_nonpos := IntegralPolynomialHeight.linear_nonpos P
    root_square := RootVsToric.root_square P
    toric_square := RootVsToric.toric_square P
    bounds := RootVsToric.bounds P
    comparison := RootVsToric.comparison P
    zero_iff := RootVsToric.zero_iff P
    zero_height := RootVsToric.zero_height P }
