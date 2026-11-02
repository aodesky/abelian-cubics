import Cubic.Counting.TraceZeroLattice
import Cubic.PoissonSummation.HeightCountingIdentification
import CubicTargets.Counting.GeneralMonic

/-!
# Proof of `lemma:traceZeroCoefficients`

Following the paper, with `α = a + bζ ∈ ℤ[ζ]`:

* `c ↦ α = (δ + 3c)/2 + 3cζ` matches the solutions of `δ² = 4N³ - 27c²` with the elements
  of norm `N³` whose `ζ`-coefficient is divisible by `3`; a solution with `δ > 0` has two
  preimages and one with `δ = 0` has one (`TraceZeroLattice.sliceEquiv`, `ncard_sol_add`).
* `ℤ[ζ]` has class number one and six units, and the number of ideals of norm `N³` is `d_M`
  (`EisensteinNormCount.card_normSet`, `EisensteinIdealCount.idealCount_cube`).
* If `e = 0`, exactly two of the six unit multiples of a generator have `ζ`-coefficient
  divisible by `3`; if `e ≥ 1`, all six do (`TraceZeroLattice.three_mul_ncard_slice`,
  `slice_eq_of_nine_dvd`).
* `δ = 0` occurs exactly when `N = 3u²`, with `c = ±2u³` (`TraceZeroLattice.ncard_zero`).

The paper's `d_M` is the explicit product over the primes dividing `M`; it is the height
coefficient `d_M` by `thm:heightZetaFunctionFormula`, which rests on the Poisson package.
-/

noncomputable section

namespace Cubic.Counting.TraceZeroCoefficients

open Cubic.Counting.GeneralMonicData Cubic.Counting.EisensteinNormCount
open Cubic.Counting.EisensteinIdealCount Cubic.Counting.TraceZeroLattice
open Cubic.PoissonSummation

theorem «lemma:traceZeroCoefficients»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.Counting.GeneralMonic.TraceZeroCoefficientsClaim := by
  intro e M hM h3
  set N : ℤ := ((3 ^ e * M : ℕ) : ℤ) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_⟩
  · have hP : Set.Finite {q : ℤ × ℤ | q ∈ sol N ∧ 0 ≤ q.2} := (sol_finite N).subset fun _ h => h.1
    haveI : Finite {q : ℤ × ℤ // q ∈ sol N ∧ 0 ≤ q.2} := hP.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (nonnegEquiv N))
  -- the elements of norm `N³` and the ideals of norm `N³`
  have hK : ((normSet (N ^ 3)).ncard : ℤ) = 6 * HeightCountingCoefficients.coefficient M := by
    have h := card_normSet ((3 ^ e * M) ^ 3) (by positivity)
    rw [Nat.card_coe_set_eq, show (((3 ^ e * M) ^ 3 : ℕ) : ℤ) = N ^ 3 by rw [hNdef]; push_cast; ring]
      at h
    have hI : (idealCount ((3 ^ e * M) ^ 3) : ℤ) = HeightCountingCoefficients.coefficient M := by
      exact_mod_cast idealCount_cube e M hM h3
    rw [h]; push_cast; rw [hI]
  have hd : (d M : ℤ) = HeightCountingCoefficients.coefficient M :=
    HeightCountingIdentification.counts_eq_coefficient hPoisson M
  have hS : (slice (N ^ 3)).ncard = (sol N).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr (sliceEquiv N)]
  have hsum := ncard_sol_add N
  have hz := ncard_zero hN1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · -- `3 ∤ N`: two of the six unit multiples, and `N = 3u²` is impossible
    have h3N : ¬ (3 : ℤ) ∣ N ^ 3 := by
      intro h
      apply h3
      have : (3 : ℤ) ∣ N := Int.prime_three.dvd_of_dvd_pow h
      rw [hNdef] at this; simpa using (Int.natCast_dvd_natCast.mp this)
    have hu : ¬ ∃ u : ℤ, 0 < u ∧ N = 3 * u ^ 2 := by
      rintro ⟨u, -, hu⟩; exact h3N ⟨9 * u ^ 6, by rw [hu]; ring⟩
    have h3S := three_mul_ncard_slice h3N
    rw [if_neg hu] at hz
    rw [if_pos rfl, hd]
    have : (3 : ℤ) * (slice (N ^ 3)).ncard = 6 * HeightCountingCoefficients.coefficient M := by
      rw [← hK]; exact_mod_cast h3S
    rw [hz, add_zero] at hsum
    have hsum' : ((sol N).ncard : ℤ) = 2 * r N := by exact_mod_cast hsum
    rw [← hS] at hsum'
    linarith
  · -- `3 ∣ N`: all six unit multiples
    have h9 : (9 : ℤ) ∣ N ^ 3 := by
      have : (3 : ℤ) ∣ N := by
        rw [hNdef]; push_cast
        exact Dvd.dvd.mul_right (dvd_pow_self 3 he.ne') _
      obtain ⟨k, hk⟩ := this
      exact ⟨3 * k ^ 3, by rw [hk]; ring⟩
    rw [slice_eq_of_nine_dvd h9] at hS
    rw [if_neg he.ne', hd]

    have hsol : ((sol N).ncard : ℤ) = 6 * HeightCountingCoefficients.coefficient M := by
      rw [← hS, hK]
    by_cases hu : ∃ u : ℤ, 0 < u ∧ N = 3 * u ^ 2
    · rw [if_pos hu] at hz
      rw [if_pos hu]
      rw [hz] at hsum
      have hsum' : ((sol N).ncard : ℤ) + 2 = 2 * r N := by exact_mod_cast hsum
      linarith
    · rw [if_neg hu] at hz
      rw [if_neg hu]
      rw [hz, add_zero] at hsum
      have hsum' : ((sol N).ncard : ℤ) = 2 * r N := by exact_mod_cast hsum
      linarith

end Cubic.Counting.TraceZeroCoefficients
