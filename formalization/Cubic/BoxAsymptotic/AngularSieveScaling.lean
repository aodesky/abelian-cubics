import Cubic.BoxAsymptotic.WeightedAngularSieve

/-! Scaling the proved maximal sieve to the larger coefficients in the dual
sum. The scale is independent of the frequency, as required by the sieve. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSieveScaling

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.AngularMaximalSums
open Cubic.BoxAsymptotic.IdealAngularData

theorem partial_mul (χ a : Ideal Integers → ℂ) (Y : ℝ) (q : ℕ) (c : ℂ) :
    partialSum χ (fun I => c * a I) Y q = c * partialSum χ a Y q := by
  simp only [partialSum, Finset.mul_sum, mul_assoc]

theorem maximal_mul (χ a : Ideal Integers → ℂ) (Y : ℝ) (c : ℂ) :
    maximal χ (fun I => c * a I) Y = ‖c‖ * maximal χ a Y := by
  apply le_antisymm
  · obtain ⟨q, hq, he⟩ := maximal_attained χ (fun I => c * a I) Y
    rw [he, partial_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (partial_le_maximal χ a Y hq) (norm_nonneg _)
  · obtain ⟨q, hq, he⟩ := maximal_attained χ a Y
    rw [he, ← norm_mul, ← partial_mul]
    exact partial_le_maximal χ (fun I => c * a I) Y hq

theorem scaled_bound {ι : Type*} (S : Finset ι) (χ : ι → Ideal Integers → ℂ)
    {Y R B : ℝ} (hB : 0 < B)
    (hsieve : ∀ b : Ideal Integers → ℂ,
      (∀ I ∈ idealBall Y, ‖b I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
      (∑ k ∈ S, maximal (χ k) b Y ^ 2) ≤ R)
    (a : Ideal Integers → ℂ)
    (ha : ∀ I ∈ idealBall Y, ‖a I‖ ≤ B / Real.sqrt (Ideal.absNorm I)) :
    (∑ k ∈ S, maximal (χ k) a Y ^ 2) ≤ B ^ 2 * R := by
  let b : Ideal Integers → ℂ := fun I => (B : ℂ)⁻¹ * a I
  have hb : ∀ I ∈ idealBall Y, ‖b I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I) := by
    intro I hI
    change ‖(B : ℂ)⁻¹ * a I‖ ≤ _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      _ ≤ B⁻¹ * (B / Real.sqrt (Ideal.absNorm I)) :=
        mul_le_mul_of_nonneg_left (ha I hI) (inv_nonneg.mpr hB.le)
      _ = _ := by rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul, one_div]
  have he : a = fun I => (B : ℂ) * b I := by
    funext I
    dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hB.ne'), one_mul]
  have hm (k : ι) : maximal (χ k) a Y = B * maximal (χ k) b Y := by
    conv_lhs => rw [he, maximal_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  simp_rw [hm, mul_pow]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hsieve b hb) (sq_nonneg B)

end Cubic.BoxAsymptotic.AngularSieveScaling
