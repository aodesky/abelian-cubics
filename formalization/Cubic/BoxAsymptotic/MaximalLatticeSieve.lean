import Cubic.BoxAsymptotic.BinaryRayEnergy

/-! Applying the binary decomposition to the angular lattice sieve. The cutoff
is an arbitrary function of the frequency, so this controls the pointwise
maximum, not merely a supremum taken after summing over frequencies. -/

noncomputable section

namespace Cubic.BoxAsymptotic.MaximalLatticeSieve

open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.LatticeSums
open Cubic.BoxAsymptotic.GroupedLargeSieve Cubic.BoxAsymptotic.RayCoefficientBounds
open Cubic.BoxAsymptotic.BinaryRayEnergy
open CubicTargets.BoxAsymptotic.BinaryDecomposition
open scoped BigOperators

theorem binary_bound
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox)
    {N : ℕ} (hN : 0 < N) (M : ℤ) {Y : ℝ} (hY : 0 < Y)
    {S : Finset (ℤ × ℤ)} (hS : S ⊆ ball Y) (c : ℤ × ℤ → ℂ)
    (J : ℕ) (q : Fin N → ℕ) (hq : ∀ n, q n < 2 ^ J) :
    (∑ n : Fin N, ‖∑ p ∈ restrict S (Finset.Icc 1 (q n)),
      c p * phase (M + (n : ℤ) + 1) (eis p)‖ ^ 2) ≤
      (J : ℝ) ^ 2 * ((N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3) *
        ∑ v ∈ rays Y, mass S c v ^ 2 := by
  classical
  let B (j b : ℕ) (n : Fin N) : ℝ :=
    ‖∑ p ∈ restrict S (block j b),
      c p * phase (M + (n : ℤ) + 1) (eis p)‖ ^ 2
  let Q : ℝ := (N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3
  let E : ℝ := ∑ v ∈ rays Y, mass S c v ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hone (n : Fin N) :
      ‖∑ p ∈ restrict S (Finset.Icc 1 (q n)),
        c p * phase (M + (n : ℤ) + 1) (eis p)‖ ^ 2 ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ∑ b ∈ Finset.range (2 ^ J), B j b n := by
    have h := hRM J (q n) (hq n)
      (byNorm S (fun p => c p * phase (M + (n : ℤ) + 1) (eis p)))
    simpa only [sum_byNorm] using h
  have hblock (j b : ℕ) : (∑ n : Fin N, B j b n) ≤
      Q * ∑ v ∈ rays Y, mass (restrict S (block j b)) c v ^ 2 := by
    exact grouped_large_sieve hLS hN M hY
      ((Finset.filter_subset _ S).trans hS) c
  have hlevel (j : ℕ) :
      (∑ b ∈ Finset.range (2 ^ J), ∑ n : Fin N, B j b n) ≤ Q * E := by
    calc
      _ ≤ ∑ b ∈ Finset.range (2 ^ J),
          Q * ∑ v ∈ rays Y, mass (restrict S (block j b)) c v ^ 2 :=
        Finset.sum_le_sum (fun b _ => hblock j b)
      _ = Q * ∑ b ∈ Finset.range (2 ^ J), ∑ v ∈ rays Y,
          mass (restrict S (block j b)) c v ^ 2 := by rw [Finset.mul_sum]
      _ ≤ Q * E := mul_le_mul_of_nonneg_left (level_energy Y S c j J) hQ
  calc
    _ ≤ ∑ n : Fin N, (J : ℝ) *
        ∑ j ∈ Finset.range J, ∑ b ∈ Finset.range (2 ^ J), B j b n :=
      Finset.sum_le_sum (fun n _ => hone n)
    _ = (J : ℝ) * ∑ j ∈ Finset.range J,
        ∑ b ∈ Finset.range (2 ^ J), ∑ n : Fin N, B j b n := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ ≤ (J : ℝ) * ∑ _j ∈ Finset.range J, Q * E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlevel j))
        (Nat.cast_nonneg _)
    _ = (J : ℝ) ^ 2 * Q * E := by simp; ring

theorem depth_bound {Y : ℝ} (hY : 1 ≤ Y) :
    ((Nat.log 2 ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log Y) := by
  have hfloor : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
  have hpow := Nat.pow_log_le_self 2 (by omega : ⌊Y⌋₊ ≠ 0)
  have hlog : (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log 2 ≤ Real.log Y := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact (by exact_mod_cast hpow :
      (2 : ℝ) ^ Nat.log 2 ⌊Y⌋₊ ≤ ⌊Y⌋₊).trans (Nat.floor_le (by linarith))
  have hl2 := Real.log_two_gt_d9
  have hlY := Real.log_nonneg hY
  have hn := Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊Y⌋₊)
  push_cast
  nlinarith

theorem log_bound {Y : ℝ} (hY : 1 ≤ Y) :
    1 + Real.log Y ≤ 3 * Real.log (2 * Y) := by
  rw [Real.log_mul (by norm_num) (by linarith)]
  have hlog := Real.log_nonneg hY
  have htwo := Real.log_two_gt_d9
  linarith

/-- The lattice version of the maximal angular estimate, for every choice of
cutoff at each frequency. The constant is independent of all the parameters. -/
theorem maximal_bound
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (M : ℤ) (Y : ℝ), 2 ≤ Y →
      ∀ (S : Finset (ℤ × ℤ)), S ⊆ ball Y → ∀ (c : ℤ × ℤ → ℂ),
        (∀ p ∈ S, ‖c p‖ ≤ 1 / Real.sqrt (EisensteinCoordinates.nrm p)) →
        ∀ (q : Fin N → ℕ), (∀ n, q n ≤ ⌊Y⌋₊) →
      (∑ n : Fin N, ‖∑ p ∈ restrict S (Finset.Icc 1 (q n)),
        c p * phase (M + (n : ℤ) + 1) (eis p)‖ ^ 2) ≤
        C * ((N : ℝ) + Y) * Real.log (2 * Y) ^ 5 := by
  obtain ⟨C, hC, henergy⟩ := energy_bound
  let d : ℝ := 4 * Real.pi / Real.sqrt 3
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨4 * C * (1 + d) * 3 ^ 5, by positivity,
    fun N hN M Y hY S hS c hc q hq => ?_⟩
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hl : 0 ≤ 1 + Real.log Y := by linarith [Real.log_nonneg hY1]
  have hl2 : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  let J := Nat.log 2 ⌊Y⌋₊ + 1
  have hcut (n : Fin N) : q n < 2 ^ J :=
    (hq n).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hj : (J : ℝ) ^ 2 ≤ 4 * (1 + Real.log Y) ^ 2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg J) (depth_bound hY1) 2
    nlinarith
  have hQ : (N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3 ≤
      (1 + d) * ((N : ℝ) + Y) := by
    calc
      _ = (N : ℝ) + d * Y := by dsimp [d]; ring
      _ ≤ _ := by nlinarith [mul_nonneg hd (Nat.cast_nonneg (α := ℝ) N)]
  have h := binary_bound hLS hRM hN M (by linarith : 0 < Y) hS c J q hcut
  calc
    _ ≤ (J : ℝ) ^ 2 * ((N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3) *
        (C * (1 + Real.log Y) ^ 3) :=
      h.trans (mul_le_mul_of_nonneg_left (henergy Y hY1 S hS c hc) (by positivity))
    _ ≤ (4 * (1 + Real.log Y) ^ 2) * ((1 + d) * ((N : ℝ) + Y)) *
        (C * (1 + Real.log Y) ^ 3) := by gcongr
    _ = (4 * C * (1 + d)) * ((N : ℝ) + Y) * (1 + Real.log Y) ^ 5 := by ring
    _ ≤ (4 * C * (1 + d)) * ((N : ℝ) + Y) * (3 * Real.log (2 * Y)) ^ 5 := by
      gcongr
      exact log_bound hY1
    _ = _ := by ring

end Cubic.BoxAsymptotic.MaximalLatticeSieve
