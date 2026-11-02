import Cubic.BoxAsymptotic.AngularUnitSums

/-! The complete local angular coefficient table at three, as a refinement of
`eq:mass`. No functional equation, large sieve, or smoothing input enters here. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularRamified

open Complex CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData
open Cubic.BoxAsymptotic.AngularLocal Cubic.BoxAsymptotic.AngularUnitSums
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.ZeroModeMass
open Cubic.Counting.EisensteinNormCount Cubic.Counting.TraceZeroLattice

theorem norm_ramified (p : ℤ × ℤ) : nrm (ramifiedMap p) = 27 * nrm p := by
  simp only [nrm, ramifiedMap]
  ring

/-- Multiplication by `λ³` bijects the full norm sets at successive powers of three.
Its image has the correct norm; equality follows from the previously proved ideal
counts and its injectivity. -/
theorem norm_image (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) :
    ramifiedMap '' normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3) =
      normSet (((3 ^ (e + 1) * M : ℕ) : ℤ) ^ 3) := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨p, hp, rfl⟩
    change nrm (ramifiedMap p) = _
    rw [norm_ramified]
    change nrm p = ((3 ^ e * M : ℕ) : ℤ) ^ 3 at hp
    rw [hp]
    push_cast
    ring
  · rw [Set.ncard_image_of_injective _ ramifiedMap_injective]
    have h := (norm_card (e + 1) M hM h3).trans (norm_card e M hM h3).symm
    exact le_of_eq (by exact_mod_cast h)
  · exact normSet_finite _

theorem sum_norm_power (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) (k : ℤ) :
    angularSum k (normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3)) =
      ramifiedPhase k ^ e * angularSum k (normSet ((M : ℤ) ^ 3)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [← norm_image e M hM h3, sum_ramified (by positivity) (fun _ h => h), ih]
    ring

theorem norm_ramifiedPhase (k : ℤ) : ‖ramifiedPhase k‖ = 1 := by
  simp [ramifiedPhase, norm_zpow]

/-- For the even frequencies used by the paper, the rotation is exactly `(-1)^(k/2)`.
This verifies the sign in the definition `y = (-1)^(k/2) 3^(-s)`. -/
theorem ramifiedPhase_even {k : ℤ} (hk : Even k) :
    ramifiedPhase k = (-1 : ℂ) ^ (k / 2) := by
  obtain ⟨j, rfl⟩ := hk
  have hj : (j + j) / 2 = j := by omega
  rw [ramifiedPhase, hj, ← two_mul j, zpow_mul]
  congr 1
  change (-I) ^ (2 : ℕ) = (-1 : ℂ)
  simp [pow_two]

/-- The precise coefficient identity which sums to `eq:Fk`. -/
theorem coefficient_power (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M)
    {k : ℤ} (hk : Even k) :
    coefficient k (3 ^ e * M) = localWeight k e * awayCoefficient k M := by
  rcases e with _ | e
  · simpa [localWeight] using coefficient_away hM h3 hk
  rcases e with _ | e
  · simpa [localWeight] using coefficient_three hM h3 hk
  have hn : 3 ^ (e + 1 + 1) * M = 3 * (3 ^ (e + 1) * M) := by ring
  have h9 : (9 : ℤ) ∣ ((3 ^ (e + 1) * M : ℕ) : ℤ) ^ 3 := by
    refine ⟨3 * (((3 ^ e * M : ℕ) : ℤ) ^ 3), ?_⟩
    push_cast
    ring
  rw [coefficient_eq_sum, hn, ← ramified_image, slice_eq_of_nine_dvd h9,
    sum_ramified (by positivity) (fun _ h => h), sum_norm_power (e + 1) M hM h3 k,
    sum_norm_even hM h3 hk]
  simp only [localWeight, show ¬ e + 1 + 1 < 2 by omega, if_false]
  split_ifs <;> ring

end Cubic.BoxAsymptotic.AngularRamified
