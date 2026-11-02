import CubicTargets.AllGaloisCounts.AllGaloisCounts
import Cubic.AllGaloisCounts.RealHeightBounds

/-! Integer-height specialization of the four Galois counts. The two
fractional-part endpoints coincide at integral height; the remaining
coefficient-box terms have degree at most two. -/

namespace Cubic.AllGaloisCounts.AllGaloisCounts
open CountData Filter Asymptotics

theorem R_nat (H : ℕ) : R H = markedVolume * (H : ℝ) ^ 4 +
    markedBoundary * (H : ℝ) ^ 3 := by
  simp [R]

theorem boxFormula_nat (H : ℕ) : boxFormula H =
    8 * (H : ℝ) ^ 6 + 4 * (H : ℝ) ^ 5 + 4 * (H : ℝ) ^ 4 +
      6 * (H : ℝ) ^ 3 + 2 * (H : ℝ) ^ 2 + 2 * (H : ℝ) + 1 := by
  have hf (j : ℕ) : (⌊(H : ℝ) ^ j⌋ : ℝ) = (H : ℝ) ^ j := by
    rw [← Nat.cast_pow, Int.floor_natCast, Int.cast_natCast]
  simp only [boxFormula, hf]
  norm_num [Finset.prod_Icc_succ_top]
  ring

theorem box_tail :
    (fun H : ℕ => 2 * (H : ℝ) ^ 2 + 2 * (H : ℝ) + 1)
      =O[atTop] (fun H : ℕ => (H : ℝ) ^ 2) := by
  apply IsBigO.of_bound 5
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 2 * (H : ℝ) ^ 2 + 2 * (H : ℝ) + 1),
    abs_of_nonneg (sq_nonneg (H : ℝ))]
  nlinarith

theorem «thm:allGaloisCounts»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.AllGaloisCounts.AllGaloisCounts.Claim := by
  refine ⟨HeightBox.galoisSet_finite,
    SplitCubicCount.«lemma:splitCubicCount».2.comp_tendsto tendsto_natCast_atTop_atTop,
    ?_, fun ε hε => ⟨?_, ?_⟩⟩
  · have h := RealHeightBounds.quadratic.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    exact h.congr_left (fun H => by simp only [Function.comp_apply]; rw [R_nat]; ring)
  · exact (CyclicCount.estimate hPoisson hCN ε hε).comp_tendsto tendsto_natCast_atTop_atTop
  · have h := (RealHeightBounds.symmetric hPoisson hCN ε hε).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have ht := box_tail.trans ((RealHeightBounds.square_isBigO ε hε).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact (h.add ht).congr_left (fun H => by
      simp only [Function.comp_apply]; rw [boxFormula_nat, R_nat]; ring)

end Cubic.AllGaloisCounts.AllGaloisCounts
