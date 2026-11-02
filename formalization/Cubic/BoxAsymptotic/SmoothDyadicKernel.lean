import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The uniformly summable dyadic kernel in `lem:smooth`. Telescoping proves
the bound without introducing any power loss in the angular scale. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothDyadicKernel

def term (u : ℝ) (j : ℕ) : ℝ :=
  u * 2 ^ j / (1 + u * 2 ^ j) ^ 2

theorem term_nonneg {u : ℝ} (hu : 0 ≤ u) (j : ℕ) : 0 ≤ term u j := by
  unfold term
  positivity

theorem telescoping_bound {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ^ 2 ≤ 2 * ((1 + x)⁻¹ - (1 + 2 * x)⁻¹) := by
  have h1 : 0 < 1 + x := by positivity
  have h2 : 0 < 1 + 2 * x := by positivity
  field_simp
  nlinarith [sq_nonneg x]

theorem partial_bound {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (∑ j ∈ Finset.range n, term u j) ≤
      2 * ((1 + u)⁻¹ - (1 + u * 2 ^ n)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := telescoping_bound (show 0 ≤ u * 2 ^ n by positivity)
    change term u n ≤ _ at ht
    rw [Finset.sum_range_succ, pow_succ]
    have he : 1 + u * (2 ^ n * 2) = 1 + 2 * (u * 2 ^ n) := by ring
    rw [he]
    linarith

theorem partial_le_two {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (∑ j ∈ Finset.range n, term u j) ≤ 2 := by
  have hi : (1 + u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ht : 0 ≤ (1 + u * 2 ^ n)⁻¹ := by positivity
  exact (partial_bound hu n).trans (by linarith)

theorem summable {u : ℝ} (hu : 0 ≤ u) : Summable (term u) :=
  summable_of_sum_range_le (term_nonneg hu) (partial_le_two hu)

theorem total_le_two {u : ℝ} (hu : 0 ≤ u) : (∑' j, term u j) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (term_nonneg hu) (partial_le_two hu)

end Cubic.BoxAsymptotic.SmoothDyadicKernel
