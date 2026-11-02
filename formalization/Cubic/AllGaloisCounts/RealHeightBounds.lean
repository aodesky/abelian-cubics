import CubicTargets.AllGaloisCounts.RealHeightBounds
import Cubic.AllGaloisCounts.CountingIdentities
import Cubic.AllGaloisCounts.MarkedLinearFactorCount
import Cubic.AllGaloisCounts.SplitCubicCount
import Cubic.AllGaloisCounts.CyclicCount

/-! Assemble the four counts for arbitrary real heights, retaining the
fractional part in the marked count and all floors in the coefficient box. -/

namespace Cubic.AllGaloisCounts.RealHeightBounds
open CountData Filter Asymptotics

theorem marked_comparison :
    (fun H : ℝ => (markedCount H : ℝ) - N .quadratic H - 3 * N .trivial H)
      =O[atTop] (fun H : ℝ => H ^ 2) := by
  apply IsBigO.of_bound 225
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H)] using
    CountingIdentities.marked_error hH

theorem quadratic :
    (fun H : ℝ => (N .quadratic H : ℝ) - (R H - 3 * splitLeading * H ^ 3))
      =O[atTop] (fun H : ℝ => H ^ 2) := by
  have h := (MarkedLinearFactorCount.«prop:markedLinearFactorCount».2.sub
    marked_comparison).sub (SplitCubicCount.«lemma:splitCubicCount».2.const_mul_left 3)
  exact h.congr_left (fun H => by ring)

theorem square_isBigO (ε : ℝ) (hε : 0 < ε) :
    (fun H : ℝ => H ^ 2) =O[atTop] (fun H : ℝ => H ^ (2 + ε)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H), one_mul,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ H) _)]
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hH (by norm_num; linarith)

theorem symmetric
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox)
    (ε : ℝ) (hε : 0 < ε) :
    (fun H : ℝ => (N .symmetric H : ℝ) -
      (boxFormula H - R H - H ^ 3 * (P (Real.log H) - 2 * splitLeading)))
      =O[atTop] (fun H : ℝ => H ^ (2 + ε)) := by
  have hs := SplitCubicCount.«lemma:splitCubicCount».2.trans (square_isBigO ε hε)
  have hq := quadratic.trans (square_isBigO ε hε)
  have hc := CyclicCount.estimate hPoisson hCN ε hε
  refine ((hs.add hq).add hc).neg_left.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  have hp : (Nat.card (cubicBox H) : ℝ) =
      (N .trivial H : ℝ) + N .quadratic H + N .cyclic H + N .symmetric H := by
    exact_mod_cast CountingIdentities.partition H
  rw [HeightBox.box_count hH] at hp
  nlinarith [hp]

theorem «rem:realHeightBounds»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.AllGaloisCounts.RealHeightBounds.Claim := by
  exact ⟨fun _ hH => HeightBox.box_count hH,
    SplitCubicCount.«lemma:splitCubicCount».2,
    MarkedLinearFactorCount.«prop:markedLinearFactorCount».2,
    quadratic, fun ε hε => ⟨CyclicCount.estimate hPoisson hCN ε hε,
      symmetric hPoisson hCN ε hε⟩⟩

end Cubic.AllGaloisCounts.RealHeightBounds
