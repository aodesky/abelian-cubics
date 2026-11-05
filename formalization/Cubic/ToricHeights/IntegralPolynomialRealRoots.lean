import Cubic.ToricHeights.IntegralPolynomialHeight
import Cubic.QuadraticCorrespondence.QuotientCubicClassification
import Cubic.Counting.CyclicPolynomialRealRoots
import Cubic.ToricHeights.RootHeightAMGM
import Mathlib.Algebra.CubicDiscriminant

/-!
# Real roots of the cubic at every integral quotient point

Follow the paper's proof of `lemma:rootVsToric`: the descended cubic
is cyclic or rationally split, and complex conjugation is trivial in the cyclic
case, so the cubic has three real roots. Comparing coefficients and applying
AM–GM to their squares gives `b² ≤ ((1 + 2A)/3)³` with `A = -a`.
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

/-- Comparing coefficients in `f = (t - r₁)(t - r₂)(t - r₃)` over the three real roots and
applying AM–GM to the `rᵢ²`. -/
theorem constant_sq_le (P : Points) :
    (constant P : ℝ) ^ 2 ≤ ((1 + 2 * -(linear P : ℝ)) / 3) ^ 3 := by
  let Q : Cubic ℝ := ⟨1, -1, linear P, constant P⟩
  have hQ : Q.a ≠ 0 := by norm_num [Q]
  have hs : (Q.toPoly.map (RingHom.id ℝ)).Splits := by
    simpa only [map_id] using real_cubic_splits P
  obtain ⟨x, y, z, hr⟩ := (Cubic.splits_iff_roots_eq_three hQ).mp hs
  have hb := Cubic.b_eq_three_roots hQ hr
  have hc := Cubic.c_eq_three_roots hQ hr
  have hd := Cubic.d_eq_three_roots hQ hr
  simp only [Q, RingHom.id_apply, one_mul] at hb hc hd
  exact RootHeightAMGM.constant_sq_le _ _ x y z (by linarith) hc.symm (by linarith)

end Cubic.ToricHeights.IntegralPolynomialRealRoots
