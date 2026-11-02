import Cubic.BoxAsymptotic.IdealLargeSieve
import Cubic.BoxAsymptotic.AngularMomentSums

/-! Real dyadic frequency endpoints for the maximal ideal sieve. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSieveFrequencies

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.IdealLargeSieve
open CubicTargets.BoxAsymptotic

def length (K : ℝ) : ℕ := (⌊2 * K⌋ - ⌊K⌋).toNat

def frequency (K : ℝ) (n : Fin (length K)) : ℤ := ⌊K⌋ + (n : ℤ) + 1

theorem floor_difference {K : ℝ} (hK : 2 ≤ K) :
    1 ≤ ⌊2 * K⌋ - ⌊K⌋ := by
  have h₁ := Int.floor_le K
  have h₂ := Int.lt_floor_add_one (2 * K)
  have h : (1 : ℝ) ≤ (⌊2 * K⌋ : ℝ) - ⌊K⌋ := by linarith
  exact_mod_cast h

theorem cast_length {K : ℝ} (hK : 2 ≤ K) :
    (length K : ℤ) = ⌊2 * K⌋ - ⌊K⌋ :=
  Int.toNat_of_nonneg (by linarith [floor_difference hK])

theorem length_pos {K : ℝ} (hK : 2 ≤ K) : 0 < length K := by
  have h := floor_difference hK
  rw [← cast_length hK] at h
  exact_mod_cast h

theorem length_le {K : ℝ} (hK : 2 ≤ K) : (length K : ℝ) ≤ 2 * K := by
  have hc : (length K : ℝ) = (⌊2 * K⌋ : ℝ) - ⌊K⌋ := by
    exact_mod_cast cast_length hK
  have hzero : (0 : ℤ) ≤ ⌊K⌋ := Int.floor_nonneg.mpr (by linarith)
  have hzeroR : (0 : ℝ) ≤ ⌊K⌋ := by exact_mod_cast hzero
  rw [hc]
  linarith [Int.floor_le (2 * K)]

theorem frequency_injective (K : ℝ) : Function.Injective (frequency K) := by
  intro i j h
  apply Fin.ext
  dsimp [frequency] at h
  omega

theorem image_frequency {K : ℝ} (hK : 2 ≤ K) :
    Finset.univ.image (frequency K) = positiveModes K := by
  classical
  ext k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, positiveModes, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, rfl⟩
    have hn : (n : ℤ) < length K := by exact_mod_cast n.isLt
    rw [cast_length hK] at hn
    dsimp [frequency]
    have h0 : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n.val
    omega
  · rintro ⟨hlo, hhi⟩
    let n : ℕ := (k - ⌊K⌋ - 1).toNat
    have hn : (n : ℤ) = k - ⌊K⌋ - 1 := Int.toNat_of_nonneg (by omega)
    have hnN : n < length K := by
      have h : (n : ℤ) < length K := by rw [cast_length hK, hn]; omega
      exact_mod_cast h
    refine ⟨⟨n, hnN⟩, ?_⟩
    dsimp [frequency]
    omega

theorem sum_frequency {K : ℝ} (hK : 2 ≤ K) (f : ℤ → ℝ) :
    (∑ n : Fin (length K), f (frequency K n)) = ∑ k ∈ positiveModes K, f k := by
  classical
  rw [← image_frequency hK, Finset.sum_image (frequency_injective K).injOn]

theorem dyadic_bound
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y →
      ∀ (S : Finset (Ideal Integers)), S ⊆ idealBall Y →
      ∀ (a : Ideal Integers → ℂ),
        (∀ I ∈ S, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
        ∀ (q : ℤ → ℕ), (∀ k, q k ≤ ⌊Y⌋₊) →
      (∑ k ∈ positiveModes K, ‖∑ I ∈ initial S (q k),
        a I * generatorPhase k I‖ ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := IdealLargeSieve.maximal_bound hLS hRM
  refine ⟨2 * C, by positivity, fun K Y hK hY S hS a ha q hq => ?_⟩
  have h := hb (length K) (length_pos hK) ⌊K⌋ Y hY S hS a ha
    (fun n => q (frequency K n)) (fun n => hq _)
  change (∑ n : Fin (length K), ‖∑ I ∈ initial S (q (frequency K n)),
    a I * generatorPhase (frequency K n) I‖ ^ 2) ≤ _ at h
  rw [sum_frequency hK (fun k =>
    ‖∑ I ∈ initial S (q k), a I * generatorPhase k I‖ ^ 2)] at h
  have hNY : (length K : ℝ) + Y ≤ 2 * (K + Y) := by
    linarith [length_le hK]
  calc
    _ ≤ C * ((length K : ℝ) + Y) * Real.log (2 * Y) ^ 5 := h
    _ ≤ C * (2 * (K + Y)) * Real.log (2 * Y) ^ 5 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNY hC.le)
        (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2 * Y)) 5)
    _ = _ := by ring

end Cubic.BoxAsymptotic.AngularSieveFrequencies
