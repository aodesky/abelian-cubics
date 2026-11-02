import Cubic.BoxAsymptotic.LocalTraceAtThree
import Cubic.BoxAsymptotic.LocalGeneratorsAtThree
import CubicTargets.BoxAsymptotic.LocalAtThree

/-!
# The complete local table `lem:local3`

The unramified row uses the two allowed signs and the primary-generator trace
calculation. The first ramified row uses the exact `λ³` image of that slice.
At higher powers, `λ⁶=-27` makes every unit associate admissible, and direct
ramified division proves exhaustiveness. The last assertion is the original
trace-class invariance. No Poisson or analytic literature input is used.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.LocalAtThree

open CubicTargets.BoxAsymptotic
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.LocalAtThreeData Cubic.BoxAsymptotic.LocalTraceAtThree
open Cubic.BoxAsymptotic.LocalGeneratorsAtThree Cubic.BoxAsymptotic.LocalNormAtThree
open Cubic.BoxAsymptotic.AngularLocalData Cubic.BoxAsymptotic.AngularLocal
open Cubic.BoxAsymptotic.ZeroModeMass

theorem zero_row {M : ℕ} (hM : ¬ 3 ∣ M) (β : ℤ × ℤ) (s : ℤ) :
    AdmissiblePair M β s ↔ TableEntry 0 M β s := by
  constructor
  · intro h
    have hp := (exists_trace_iff M β).mp ⟨s, h⟩
    rw [admissible_away_three hM, slice_eq_primary_union hM] at hp
    rcases hp with hp | ⟨α, hα, rfl⟩
    · exact Or.inl ⟨hp, (primary_trace_iff hp s).mp h⟩
    · exact Or.inr ⟨α, hα, rfl, (negative_primary_trace_iff hα s).mp h⟩
  · rintro (⟨hp, hs⟩ | ⟨α, hα, rfl, hs⟩)
    · exact (primary_trace_iff hp s).mpr hs
    · exact (negative_primary_trace_iff hα s).mpr hs

theorem one_row {M : ℕ} (hM : ¬ 3 ∣ M) (β : ℤ × ℤ) (s : ℤ) :
    AdmissiblePair (3 * M) β s ↔ TableEntry 1 M β s := by
  rw [pair_three_iff, ← ramified_image, slice_eq_primary_union hM]
  apply and_congr _ Iff.rfl
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with hq | ⟨α, hα, rfl⟩
    · exact ⟨q, hq, Or.inl (coord_ramified q)⟩
    · refine ⟨α, hα, Or.inr ?_⟩
      rw [coord_ramified, coord_neg]
      ring
  · rintro ⟨α, hα, hp | hp⟩
    · refine ⟨α, Or.inl hα, ?_⟩
      apply coord_injective
      exact (coord_ramified α).trans hp.symm
    · refine ⟨-α, Or.inr ⟨α, hα, rfl⟩, ?_⟩
      apply coord_injective
      rw [coord_ramified, coord_neg, hp]
      ring

/-- At `e≥2`, every element of the required norm satisfies the local conditions. -/
theorem admissible_high (e M : ℕ) :
    admissible (3 ^ (e + 2) * M) = normSet (((3 ^ (e + 2) * M : ℕ) : ℤ) ^ 3) := by
  ext p
  constructor
  · exact fun h => h.1
  · intro hp
    have hpre := hp
    rw [← iterate_norm_image (e + 2) M] at hpre
    obtain ⟨q, _, rfl⟩ := hpre
    have hd := iterate_divisible e q
    have hn : 3 ^ (e + 2) * M = 3 * (3 ^ (e + 1) * M) := by ring
    rw [hn, admissible_three]
    refine ⟨?_, dvd_trans (by norm_num : (3 : ℤ) ∣ 27) hd.2, ?_⟩
    · simpa only [hn, Nat.cast_mul, Nat.cast_ofNat] using hp
    · exact dvd_sub (dvd_mul_of_dvd_right hd.1 2) hd.2

theorem high_row (e : ℕ) {M : ℕ} (hM : ¬ 3 ∣ M) (β : ℤ × ℤ) (s : ℤ) :
    AdmissiblePair (3 ^ (e + 2) * M) β s ↔ TableEntry (e + 2) M β s := by
  have hn : 3 ^ (e + 2) * M = 3 * (3 ^ (e + 1) * M) := by ring
  rw [hn, pair_three_iff, ← hn, admissible_high, normSet_generators (e + 2) hM]
  rfl

/-- The full statement of `lem:local3`, including all three rows and every trace
in its specified residue class. -/
theorem «lem:local3» : LocalAtThreeClaim := by
  constructor
  · intro e M hM β s
    rcases e with _ | _ | e
    · simpa only [pow_zero, one_mul] using zero_row hM β s
    · simpa only [pow_one] using one_row hM β s
    · exact high_row e hM β s
  · exact fun _ _ _ h₀ s => trace_class h₀ s

end Cubic.BoxAsymptotic.LocalAtThree
