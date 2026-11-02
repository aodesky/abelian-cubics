import Cubic.ToricHeights.IntegralPolynomialHeight
import Cubic.QuadraticCorrespondence.QuotientCubicClassification
import Cubic.Counting.CyclicPolynomialRealRoots

/-!
# Real roots of the cubic at every integral quotient point

Follow the paper's proof of `lemma:rootVsToric`: the descended cubic
is cyclic or rationally split; complex conjugation is trivial in the cyclic
case; the discriminant is the product of squared real root differences.
The norm/trace discriminant-square calculation is not used here.
-/

noncomputable section

namespace Cubic.ToricHeights.IntegralPolynomialRealRoots

open IntegralPolynomialData IntegralPolynomialHeight Polynomial
open Cubic.QuadraticCorrespondence

theorem real_cubic_splits (P : Points) :
    (⟨1, -1, (linear P : ℝ), (constant P : ℝ)⟩ : Cubic ℝ).toPoly.Splits := by
  have hs : ((polynomial P).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) |>.Splits := by
    rw [polynomial_descended]
    rcases QuotientCubicClassification.cyclic_or_splits P.val with hc | hs
    · exact Cubic.Counting.CyclicPolynomialRealRoots.splits_real hc
    · exact hs.map _
  simpa [polynomial, Cubic.Counting.PolynomialCountData.traceOneCubic,
    Cubic.toPoly, sub_eq_add_neg] using hs

theorem discriminant_nonneg (P : Points) :
    0 ≤ (linear P : ℝ) ^ 2 - 4 * (linear P : ℝ) ^ 3 +
      (4 - 18 * (linear P : ℝ)) * constant P - 27 * (constant P : ℝ) ^ 2 := by
  let Q : Cubic ℝ := ⟨1, -1, linear P, constant P⟩
  have hQ : Q.a ≠ 0 := by norm_num [Q]
  have hs : (Q.toPoly.map (RingHom.id ℝ)).Splits := by
    simpa only [map_id] using real_cubic_splits P
  obtain ⟨x, y, z, hr⟩ := (Cubic.splits_iff_roots_eq_three hQ).mp hs
  have hd := Cubic.discr_eq_prod_three_roots hQ hr
  simp only [Q, RingHom.id_apply, one_mul] at hd
  rw [← RootHeightDiscriminant.discriminant_formula, hd]
  exact sq_nonneg _

end Cubic.ToricHeights.IntegralPolynomialRealRoots
