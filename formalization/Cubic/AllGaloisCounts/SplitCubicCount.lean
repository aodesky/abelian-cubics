import CubicTargets.AllGaloisCounts.SplitCubicCount
import Cubic.AllGaloisCounts.SplitRepeated
import Cubic.AllGaloisCounts.SplitTraceCount

/-! `lemma:splitCubicCount`: sum the trace ellipses and divide by six;
the repeated-root orderings contribute only `O(H²)`. -/

namespace Cubic.AllGaloisCounts.SplitCubicCount
open CountData Filter Asymptotics

theorem estimate : ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
    |(N .trivial H : ℝ) - splitLeading * H ^ 3| ≤ K * H ^ 2 := by
  obtain ⟨K, hK⟩ := SplitTraceCount.triples_bound
  refine ⟨(K + 375) / 6, fun H hH => ?_⟩
  have h := abs_add_le (6 * (N .trivial H : ℝ) - Nat.card (SplitOrbits.Triples H))
    ((Nat.card (SplitOrbits.Triples H) : ℝ) - 6 * splitLeading * H ^ 3)
  have he : 6 * (N .trivial H : ℝ) - Nat.card (SplitOrbits.Triples H) +
      ((Nat.card (SplitOrbits.Triples H) : ℝ) - 6 * splitLeading * H ^ 3) =
      6 * ((N .trivial H : ℝ) - splitLeading * H ^ 3) := by ring
  rw [he, abs_mul] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)] at h
  nlinarith [SplitRepeated.six_count_error hH, hK H hH]

theorem «lemma:splitCubicCount» : CubicTargets.AllGaloisCounts.SplitCubicCount.Claim := by
  refine ⟨HeightBox.galoisSet_finite .trivial, ?_⟩
  obtain ⟨K, hK⟩ := estimate
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H)] using hK H hH
end Cubic.AllGaloisCounts.SplitCubicCount
