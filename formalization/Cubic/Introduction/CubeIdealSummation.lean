import Cubic.Introduction.CubeIdealEuler
import Mathlib.Algebra.Order.Floor.Semifield

/-! Removing the ramified prime from the actual cube-norm ideal count
is the exact difference `S(X) - S(X/3)`. -/

noncomputable section

namespace Cubic.Introduction.CubeIdealSummation

open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.PoissonSummation CubeIdealEuler

theorem coefficient_three_mul (n : ℕ) :
    allCoefficient (3 * n) = allCoefficient n := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hc : Nat.Coprime 3 m := Nat.prime_three.coprime_iff_not_dvd.mpr hm
  rw [show 3 * (3 ^ e * m) = 3 ^ (e + 1) * m by ring,
    multiplicative.map_mul_of_coprime (hc.pow_left _),
    multiplicative.map_mul_of_coprime (hc.pow_left _), three_power, three_power]

theorem away_coefficient (n : ℕ) :
    (HeightCountingCoefficients.coefficient n : ℂ) =
      if 3 ∣ n then 0 else allCoefficient n := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    Cubic.Counting.EisensteinIdealCount.cubeCount_eq_coefficient
  simpa [Cubic.Counting.EisensteinIdealCount.cubeCount, allCoefficient] using h.symm

theorem divisible_sum (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => 3 ∣ n), allCoefficient n =
      ∑ n ∈ Finset.Icc 1 (N / 3), allCoefficient n := by
  classical
  have he : (Finset.Icc 1 N).filter (fun n => 3 ∣ n) =
      (Finset.Icc 1 (N / 3)).image (fun n => 3 * n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn, hN⟩, ⟨k, rfl⟩⟩
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, ⟨hk, hN⟩, rfl⟩
      exact ⟨by omega, dvd_mul_right _ _⟩
  rw [he, Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
  exact Finset.sum_congr rfl (fun n _ => coefficient_three_mul n)

theorem finite_difference (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (HeightCountingCoefficients.coefficient n : ℂ) =
      (∑ n ∈ Finset.Icc 1 N, allCoefficient n) -
        ∑ n ∈ Finset.Icc 1 (N / 3), allCoefficient n := by
  classical
  simp_rw [away_coefficient]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← divisible_sum N]
  have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
    (fun n => 3 ∣ n) (fun n => allCoefficient n)
  linear_combination h

theorem summatory_difference (X : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (HeightCountingCoefficients.coefficient n : ℂ) =
      CubeIdealSumData.summatory E X - CubeIdealSumData.summatory E (X / 3) := by
  have hfloor : ⌊X / 3⌋₊ = ⌊X⌋₊ / 3 := by
    simpa using Nat.floor_div_natCast X 3
  simp only [CubeIdealSumData.summatory, coefficient_eq, hfloor]
  exact finite_difference _

end Cubic.Introduction.CubeIdealSummation
