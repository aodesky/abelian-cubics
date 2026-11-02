import Cubic.ToricHeights.IntegralPolynomialRealRoots
import CubicTargets.ToricHeights.RootVsToric

/-!
# Root height and toric height

Following the paper, the split/cyclic classification of the descended cubic
and complex conjugation give real roots, hence a nonnegative discriminant. The
assembly below then follows the paper's discriminant square completion.
`claim_via_discriminant_square` applies the same assembly with the discriminant
bound obtained instead from the norm/trace discriminant-square identity; it is
an alternative proof and is not used by the labelled result.
-/

noncomputable section

namespace Cubic.ToricHeights.RootVsToric

open IntegralPolynomialData IntegralPolynomialHeight Polynomial

/-- The discriminant bound, the input common to both proofs. -/
def DiscriminantNonneg : Prop := ∀ P : Points,
  0 ≤ (linear P : ℝ) ^ 2 - 4 * (linear P : ℝ) ^ 3 +
    (4 - 18 * (linear P : ℝ)) * constant P - 27 * (constant P : ℝ) ^ 2

section Assembly

variable (hdiscr : DiscriminantNonneg)

include hdiscr

private theorem root_formula (P : Points) : rootHeight P = Real.sqrt (-(linear P : ℝ)) :=
  RootHeightDiscriminant.rootHeight_eq_sqrt _ _ (linear_nonpos P) (hdiscr P)

theorem root_nonneg (P : Points) : 0 ≤ rootHeight P := by
  rw [root_formula hdiscr]
  exact Real.sqrt_nonneg _

theorem root_square (P : Points) : rootHeight P ^ 2 = -(linear P : ℝ) := by
  rw [root_formula hdiscr, Real.sq_sqrt]
  exact_mod_cast neg_nonneg.mpr (linear_nonpos P)

theorem toric_square (P : Points) : toricHeight P ^ 2 = 1 + 3 * rootHeight P ^ 2 := by
  rw [toricHeight_square, root_square hdiscr]
  ring

theorem bounds (P : Points) (B : ℝ) (hB : 0 ≤ B) :
    rootHeight P ≤ B ↔ toricHeight P ≤ Real.sqrt (1 + 3 * B ^ 2) := by
  rw [← sq_le_sq₀ (root_nonneg hdiscr P) hB,
    ← sq_le_sq₀ (toricHeight_nonneg P) (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : 0 ≤ 1 + 3 * B ^ 2), toric_square hdiscr]
  constructor <;> intro h <;> linarith

theorem comparison (P : Points) : max 1 (rootHeight P) ≤ toricHeight P ∧
    toricHeight P ≤ 2 * max 1 (rootHeight P) := by
  have hH := toricHeight_nonneg P
  have hh := root_nonneg hdiscr P
  have hs := toric_square hdiscr P
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
      have := root_square hdiscr P
      rw [h] at this
      have : (linear P : ℝ) = 0 := by nlinarith
      exact_mod_cast this
    have hb : constant P = 0 := by
      apply RootHeightDiscriminant.zero_constant
      simpa only [ha, Int.cast_zero, zero_pow (by decide : 2 ≠ 0),
        zero_pow (by decide : 3 ≠ 0), mul_zero, zero_sub, sub_zero, zero_add] using
        hdiscr P
    simp [polynomial, Counting.PolynomialCountData.traceOneCubic, ha, hb]
  · intro h
    change Counting.PolynomialCountData.rootHeight (polynomial P) = 0
    rw [h]
    simp [Counting.PolynomialCountData.rootHeight]

theorem zero_height (P : Points) (h : rootHeight P = 0) : toricHeight P = 1 := by
  have hs := toric_square hdiscr P
  rw [h] at hs
  nlinarith [toricHeight_nonneg P]

theorem claim_of_discriminant_nonneg : CubicTargets.ToricHeights.RootVsToric.Claim := by
  intro P
  exact {
    descended := IntegralPolynomialHeight.polynomial_descended P
    height_real := IntegralPolynomialHeight.height_real P
    linear_nonpos := IntegralPolynomialHeight.linear_nonpos P
    root_square := RootVsToric.root_square hdiscr P
    toric_square := RootVsToric.toric_square hdiscr P
    bounds := RootVsToric.bounds hdiscr P
    comparison := RootVsToric.comparison hdiscr P
    zero_iff := RootVsToric.zero_iff hdiscr P
    zero_height := RootVsToric.zero_height hdiscr P }

end Assembly

/-- Alternative proof, via the discriminant-square identity rather than the paper's
real-root argument. -/
theorem claim_via_discriminant_square : CubicTargets.ToricHeights.RootVsToric.Claim :=
  claim_of_discriminant_nonneg IntegralPolynomialHeight.discriminant_nonneg

end Cubic.ToricHeights.RootVsToric

/-- The full height-comparison lemma, using the paper's real-root argument. -/
theorem Cubic.ToricHeights.«lemma:rootVsToric» : CubicTargets.ToricHeights.RootVsToric.Claim :=
  RootVsToric.claim_of_discriminant_nonneg IntegralPolynomialRealRoots.discriminant_nonneg
