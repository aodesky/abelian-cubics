import Cubic.BoxAsymptotic.AngularMomentSums
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summing the dyadic approximate-functional-equation bounds

The summable majorant is polynomial in the dyadic index and geometric in its
decay.  In particular this step introduces no `K^ε`.  The analytic estimates
which supply the individual block bounds are separate proof obligations.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularMomentDyadic

open Cubic.BoxAsymptotic.AngularMomentData
open scoped BigOperators

def weight (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ j

theorem weight_nonneg (j : ℕ) : 0 ≤ weight j := by unfold weight; positivity

theorem weight_summable : Summable weight := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one 3
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp_injective Nat.succ_injective
  convert h.mul_right 2 using 1
  funext j
  simp only [Function.comp_apply, Nat.cast_succ, weight, pow_succ]
  ring

def totalWeight : ℝ := ∑' j, weight j

theorem totalWeight_pos : 0 < totalWeight := by
  have h := weight_summable.le_tsum 0 (fun j _ => weight_nonneg j)
  norm_num [weight] at h
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h

/-- The triangle inequality for the infinite sequence of dyadic blocks. -/
theorem norm_hasSum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → E} {x : E} (hv : HasSum v x) {C : ℝ}
    (hb : ∀ j, ‖v j‖ ≤ C * weight j) : ‖x‖ ≤ C * totalWeight := by
  have hs : Summable (fun j => ‖v j‖) :=
    (weight_summable.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    ‖x‖ = ‖∑' j, v j‖ := by rw [hv.tsum_eq]
    _ ≤ ∑' j, ‖v j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j, C * weight j := hs.tsum_le_tsum hb (weight_summable.mul_left C)
    _ = C * totalWeight := by rw [tsum_mul_left]; rfl

/-- Squaring the Hilbert-space bound gives the second moment. -/
theorem square_sum_le {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (v : ℕ → EuclideanSpace ℂ ι)
    (hv : HasSum v (WithLp.toLp 2 a)) {C B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖v j‖ ≤ C * Real.sqrt B * weight j) :
    (∑ i, ‖a i‖ ^ 2) ≤ (C * totalWeight) ^ 2 * B := by
  have h := norm_hasSum_le hv hb
  have hsq := pow_le_pow_left₀ (norm_nonneg (WithLp.toLp 2 a)) h 2
  rw [PiLp.norm_sq_eq_of_L2] at hsq
  have he : (C * Real.sqrt B * totalWeight) ^ 2 = (C * totalWeight) ^ 2 * B := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hB]
    ring
  rw [he] at hsq
  exact hsq

/-- Finite-dimensional assembly from coordinate limits and block mean squares.
Absolute summability follows from the block bounds; it is not an extra premise. -/
theorem square_limit_le {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (b : ℕ → ι → ℂ) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hl : ∀ i, Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), b j i)
      Filter.atTop (nhds (a i)))
    (hb : ∀ j, (∑ i, ‖b j i‖ ^ 2) ≤ M * weight j ^ 2 * B) :
    (∑ i, ‖a i‖ ^ 2) ≤ (Real.sqrt M * totalWeight) ^ 2 * B := by
  let v : ℕ → EuclideanSpace ℂ ι := fun j => WithLp.toLp 2 (b j)
  have hn (j : ℕ) : ‖v j‖ ≤ Real.sqrt M * Real.sqrt B * weight j := by
    have hs : ‖v j‖ ^ 2 ≤ M * weight j ^ 2 * B := by
      simpa only [PiLp.norm_sq_eq_of_L2] using hb j
    have he : (Real.sqrt M * Real.sqrt B * weight j) ^ 2 = M * weight j ^ 2 * B := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hB]
      ring
    have hp : 0 ≤ Real.sqrt M * Real.sqrt B * weight j := by
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (weight_nonneg j)
    nlinarith [norm_nonneg (v j)]
  have hs : Summable (fun j => ‖v j‖) :=
    (weight_summable.mul_left (Real.sqrt M * Real.sqrt B)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hn
  have hc (i : ι) : HasSum (fun j => b j i) (a i) := by
    have hi : Summable (fun j => ‖b j i‖) := hs.of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun j => PiLp.norm_apply_le (v j) i)
    exact (hasSum_iff_tendsto_nat_of_summable_norm hi).mpr
      ((Filter.tendsto_add_atTop_iff_nat 1).mp (hl i))
  have hv : HasSum v (WithLp.toLp 2 a) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.hasSum
      (Pi.hasSum.mpr hc)
  exact square_sum_le a v hv hB hn

/-- The slightly weaker logarithmic exponent six avoids fractional powers in
the formal dyadic bookkeeping and is allowed by the paper's unspecified `A`. -/
theorem scale_six {K : ℝ} (hK : 2 ≤ K) (t : ℝ) :
    (K + |t|) * (Real.log (2 * K + 2 * |t|)) ^ 6 ≤ momentScale 6 K t := by
  have ht : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hp : 1 + |t| ≤ (1 + |t|) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht (by norm_num : 1 ≤ 6)
  have hKY : K + |t| ≤ K * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hmul := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ K)
  exact mul_le_mul_of_nonneg_right (hKY.trans hmul) (by positivity)

end Cubic.BoxAsymptotic.AngularMomentDyadic
