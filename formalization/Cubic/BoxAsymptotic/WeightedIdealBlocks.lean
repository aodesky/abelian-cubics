import Cubic.BoxAsymptotic.HeckeWeightedSeries
import Cubic.BoxAsymptotic.AngularMomentDyadic

/-! The actual dyadic blocks in the AFE proof. Their finite sums telescope
to norm cutoffs. Absolute convergence then identifies their infinite sum
with the original ideal series, once the block majorant is supplied. -/

noncomputable section

namespace Cubic.BoxAsymptotic.WeightedIdealBlocks

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.WeightedIdealSums
open Cubic.BoxAsymptotic.HeckeWeightedSeries
open Filter
open scoped Topology

def block (χ a : Ideal Integers → ℂ) (Y : ℝ) (w : ℝ → ℂ) : ℕ → ℂ
  | 0 => initialWeighted χ a Y w
  | j + 1 => intervalWeighted χ a ((2 : ℝ) ^ j * Y) ((2 : ℝ) ^ (j + 1) * Y) w

theorem interval_sub (χ a : Ideal Integers → ℂ) (w : ℝ → ℂ) {X Y : ℝ} (hXY : X ≤ Y) :
    intervalWeighted χ a X Y w = initialWeighted χ a Y w - initialWeighted χ a X w := by
  classical
  have hsub : idealBall X ⊆ idealBall Y := fun I hI => mem_idealBall.mpr
    ⟨(mem_idealBall.mp hI).1, (mem_idealBall.mp hI).2.trans hXY⟩
  have he : (idealBall Y).filter (fun I => X < (Ideal.absNorm I : ℝ)) = idealBall Y \ idealBall X := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_idealBall, not_and, not_le]
    constructor
    · rintro ⟨⟨hI, hY⟩, hX⟩
      exact ⟨⟨hI, hY⟩, fun _ => hX⟩
    · rintro ⟨⟨hI, hY⟩, hX⟩
      exact ⟨⟨hI, hY⟩, hX hI⟩
  rw [intervalWeighted, he]
  apply (eq_sub_iff_add_eq).mpr
  exact Finset.sum_sdiff hsub

theorem partial_blocks (χ a : Ideal Integers → ℂ) (Y : ℝ) (hY : 0 ≤ Y) (w : ℝ → ℂ) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), block χ a Y w i) = initialWeighted χ a ((2 : ℝ) ^ j * Y) w := by
  induction j with
  | zero => simp [block]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, block, interval_sub χ a w]
    · abel
    · have hp : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
      exact mul_le_mul_of_nonneg_right hp hY

theorem hasSum_blocks (χ : Ideal Integers → ℂ) (u : ℂ) (Y : ℝ) (hY : 0 < Y) (w : ℝ → ℂ)
    (habs : Summable (fun I => ‖term χ u w I‖))
    (hblocks : Summable (fun j => ‖block χ (HeckeNormWeights.coefficient u) Y w j‖)) :
    HasSum (block χ (HeckeNormWeights.coefficient u) Y w) (∑' I, term χ u w I) := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm hblocks).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hscale : Tendsto (fun j : ℕ => (2 : ℝ) ^ j * Y) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hY
  have hh := (initial_limit χ u w habs).comp hscale
  simpa only [partial_blocks χ (HeckeNormWeights.coefficient u) Y hY.le w, Function.comp_def] using hh

end Cubic.BoxAsymptotic.WeightedIdealBlocks
