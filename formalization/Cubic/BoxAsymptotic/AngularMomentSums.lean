import Cubic.BoxAsymptotic.AngularMomentData
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Frequency bookkeeping for `lem:moment`: the real dyadic endpoints, the
passage from `k` to `3k`, and the two signs of the Fourier frequencies. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularMomentSums

open Cubic.BoxAsymptotic.AngularMomentData
open scoped BigOperators

theorem mem_positiveModes {K : ℝ} {k : ℤ} :
    k ∈ positiveModes K ↔ K < k ∧ (k : ℝ) ≤ 2 * K := by
  simp only [positiveModes, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

theorem mem_evenModes {K : ℝ} {k : ℤ} :
    k ∈ evenModes K ↔ (K < k ∧ (k : ℝ) ≤ 2 * K) ∧ Even k := by
  simp only [evenModes, Finset.mem_filter, mem_positiveModes]

theorem positive_of_mem {K : ℝ} (hK : 0 ≤ K) {k : ℤ}
    (hk : k ∈ positiveModes K) : 0 < k := by
  have := (mem_positiveModes.mp hk).1
  exact_mod_cast (lt_of_le_of_lt hK this)

theorem mem_signedModes {K : ℝ} (hK : 0 ≤ K) {k : ℤ} :
    k ∈ signedModes K ↔ K < |(k : ℝ)| ∧ |(k : ℝ)| ≤ 2 * K := by
  simp only [signedModes, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hk | ⟨j, hj, rfl⟩)
    · have hp := positive_of_mem hK hk
      simpa [abs_of_pos (show (0 : ℝ) < k by exact_mod_cast hp)] using
        mem_positiveModes.mp hk
    · have hp := positive_of_mem hK hj
      simpa [abs_of_pos (show (0 : ℝ) < j by exact_mod_cast hp)] using
        mem_positiveModes.mp hj
  · intro hk
    by_cases hp : 0 ≤ k
    · left
      have hpR : (0 : ℝ) ≤ k := by exact_mod_cast hp
      exact mem_positiveModes.mpr (by simpa only [abs_of_nonneg hpR] using hk)
    · right
      refine ⟨-k, ?_, neg_neg k⟩
      apply mem_positiveModes.mpr
      simpa [abs_of_neg (show (k : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hp))] using hk

theorem signed_sum (K : ℝ) (hK : 0 ≤ K) (f : ℤ → ℝ) :
    (∑ k ∈ signedModes K, f k) =
      (∑ k ∈ positiveModes K, f k) + ∑ k ∈ positiveModes K, f (-k) := by
  classical
  have hd : Disjoint (positiveModes K) ((positiveModes K).image (fun k => -k)) := by
    rw [Finset.disjoint_left]
    intro k hk hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have := positive_of_mem hK hk
    have := positive_of_mem hK hj
    omega
  rw [signedModes, Finset.sum_union hd, Finset.sum_image]
  intro i _ j _ h
  exact neg_injective h

theorem triple_mem {K : ℝ} {k : ℤ} (hk : k ∈ evenModes K) :
    3 * k ∈ evenModes (3 * K) := by
  obtain ⟨⟨hlo, hhi⟩, he⟩ := mem_evenModes.mp hk
  apply mem_evenModes.mpr
  refine ⟨?_, he.mul_left 3⟩
  push_cast
  constructor <;> linarith

theorem triple_sum_le (K : ℝ) (f : ℤ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ k ∈ evenModes K, f (3 * k)) ≤ ∑ k ∈ evenModes (3 * K), f k := by
  classical
  have hi : Set.InjOn (fun k : ℤ => 3 * k) (evenModes K) := by
    intro i _ j _ h
    change 3 * i = 3 * j at h
    omega
  rw [← Finset.sum_image hi]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact triple_mem hk
  · intro j _ _
    exact hf j

theorem scale_nonneg (A : ℕ) {K : ℝ} (hK : 2 ≤ K) (t : ℝ) :
    0 ≤ momentScale A K t := by
  have hl : 0 ≤ Real.log (2 * K + 2 * |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  exact mul_nonneg (mul_nonneg (by linarith) (by positivity)) (pow_nonneg hl _)

@[simp] theorem scale_neg (A : ℕ) (K t : ℝ) :
    momentScale A K (-t) = momentScale A K t := by simp [momentScale]

theorem scale_triple (A : ℕ) {K : ℝ} (hK : 2 ≤ K) (t : ℝ) :
    momentScale A (3 * K) t ≤ 3 ^ (A + 1) * momentScale A K t := by
  set x := 2 * K + 2 * |t|
  have hx : 4 ≤ x := by dsimp [x]; linarith [abs_nonneg t]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have harg : 2 * (3 * K) + 2 * |t| ≤ x ^ 3 := by
    have : 2 * (3 * K) + 2 * |t| ≤ 3 * x := by dsimp [x]; linarith [abs_nonneg t]
    have hx2 : 3 ≤ x ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hx2 (by linarith : 0 ≤ x)
    nlinarith
  have hl : Real.log (2 * (3 * K) + 2 * |t|) ≤ 3 * Real.log x := by
    have h := Real.log_le_log (by linarith [abs_nonneg t] :
      0 < 2 * (3 * K) + 2 * |t|) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hl0 : 0 ≤ Real.log (2 * (3 * K) + 2 * |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hp := pow_le_pow_left₀ hl0 hl A
  have hc : 0 ≤ 3 * K * (1 + |t|) ^ A := by positivity
  calc
    momentScale A (3 * K) t ≤ (3 * K * (1 + |t|) ^ A) * (3 * Real.log x) ^ A :=
      mul_le_mul_of_nonneg_left hp hc
    _ = 3 ^ (A + 1) * momentScale A K t := by
      rw [mul_pow, pow_succ]
      simp only [momentScale, x]
      ring

end Cubic.BoxAsymptotic.AngularMomentSums
