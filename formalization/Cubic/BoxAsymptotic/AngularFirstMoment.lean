import Cubic.BoxAsymptotic.AngularMomentSums

/-!
# The second-moment to first-moment step in `lem:moment`

This isolates the last paragraph of the proof. The second moment and the
pointwise factorization bound are explicit premises of this supporting result;
neither is a literature hypothesis or a completed proof of the full lemma.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularFirstMoment

open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open scoped BigOperators

/-- The positive-frequency estimate. The inequality `2ab ≤ a²+b²` is sufficient
here because the two second moments have the same scale, up to an absolute
constant. It gives the same conclusion as Cauchy--Schwarz in the paper. -/
theorem positive_bound (L F : ℤ → ℂ → ℂ) (A : ℕ) (C₂ Cᵣ : ℝ)
    (hC₂ : 0 ≤ C₂) (hCᵣ : 0 ≤ Cᵣ)
    (hsecond : ∀ (K t σ : ℝ), 2 ≤ K → 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      (∑ k ∈ evenModes K, ‖L k (σ + t * Complex.I)‖ ^ 2) ≤
        C₂ * momentScale A K t)
    (hfactor : ∀ (k : ℤ) (t η : ℝ), 0 < k → Even k → 0 < η → η ≤ 1 / 4 →
      ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖ ≤
        Cᵣ * η⁻¹ ^ 4 * ‖L k ((1 / 2 + η : ℝ) + t * Complex.I)‖ *
          ‖L (3 * k) ((1 / 2 + η : ℝ) + t * Complex.I)‖)
    (hodd : ∀ (k : ℤ) (t η : ℝ), ¬ Even k → 0 < η →
      F k ((1 / 2 + η : ℝ) + t * Complex.I) = 0)
    (K t η : ℝ) (hK : 2 ≤ K) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    (∑ k ∈ positiveModes K, ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖) ≤
      Cᵣ * C₂ * (1 + 3 ^ (A + 1)) * η⁻¹ ^ 4 * momentScale A K t := by
  classical
  set s : ℂ := (1 / 2 + η : ℝ) + t * Complex.I
  have hsum : (∑ k ∈ positiveModes K, ‖F k s‖) = ∑ k ∈ evenModes K, ‖F k s‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hke
    have he : ¬ Even k := by
      intro he
      exact hke (Finset.mem_filter.mpr ⟨hk, he⟩)
    change ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖ = 0
    rw [hodd k t η he hη, norm_zero]
  have h₁ := hsecond K t (1 / 2 + η) hK (by linarith) (by linarith)
  have h₃ := (triple_sum_le K (fun k => ‖L k s‖ ^ 2) (fun _ => sq_nonneg _)).trans
    (hsecond (3 * K) t (1 / 2 + η) (by linarith) (by linarith) (by linarith))
  have hscale := mul_le_mul_of_nonneg_left (scale_triple A hK t) hC₂
  have htot : (∑ k ∈ evenModes K, (‖L k s‖ ^ 2 + ‖L (3 * k) s‖ ^ 2)) ≤
      C₂ * (1 + 3 ^ (A + 1)) * momentScale A K t := by
    rw [Finset.sum_add_distrib]
    dsimp only [s] at h₃ ⊢
    nlinarith only [h₁, h₃, hscale]
  have hq : 0 ≤ Cᵣ * η⁻¹ ^ 4 := mul_nonneg hCᵣ (by positivity)
  rw [hsum]
  calc
    (∑ k ∈ evenModes K, ‖F k s‖) ≤
        ∑ k ∈ evenModes K, (Cᵣ * η⁻¹ ^ 4) *
          (‖L k s‖ ^ 2 + ‖L (3 * k) s‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk', he⟩ := mem_evenModes.mp hk
      have hkpos : 0 < k := positive_of_mem (by linarith) (mem_positiveModes.mpr hk')
      have hf := hfactor k t η hkpos he hη hη'
      have hab : ‖L k s‖ * ‖L (3 * k) s‖ ≤ ‖L k s‖ ^ 2 + ‖L (3 * k) s‖ ^ 2 := by
        nlinarith [sq_nonneg (‖L k s‖ - ‖L (3 * k) s‖), sq_nonneg ‖L k s‖,
          sq_nonneg ‖L (3 * k) s‖]
      exact hf.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab hq)
    _ = (Cᵣ * η⁻¹ ^ 4) *
        (∑ k ∈ evenModes K, (‖L k s‖ ^ 2 + ‖L (3 * k) s‖ ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (Cᵣ * η⁻¹ ^ 4) * (C₂ * (1 + 3 ^ (A + 1)) * momentScale A K t) :=
      mul_le_mul_of_nonneg_left htot hq
    _ = _ := by ring

/-- Add the negative frequencies using the conjugation identity at the
reflected point `σ-it`, rather than incorrectly keeping `t` fixed. -/
theorem signed_bound (F : ℤ → ℂ → ℂ) (A : ℕ) (C : ℝ)
    (hpositive : ∀ (K t η : ℝ), 2 ≤ K → 0 < η → η ≤ 1 / 4 →
      (∑ k ∈ positiveModes K, ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖) ≤
        C * η⁻¹ ^ 4 * momentScale A K t)
    (hconj : ∀ (k : ℤ) (t η : ℝ), 0 < k → 0 < η →
      F (-k) ((1 / 2 + η : ℝ) + t * Complex.I) =
        star (F k ((1 / 2 + η : ℝ) + (-t) * Complex.I)))
    (K t η : ℝ) (hK : 2 ≤ K) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖) ≤
      (2 * C) * η⁻¹ ^ 4 * momentScale A K t := by
  rw [signed_sum K (by linarith)]
  have hn : (∑ k ∈ positiveModes K, ‖F (-k) ((1 / 2 + η : ℝ) + t * Complex.I)‖) =
      ∑ k ∈ positiveModes K, ‖F k ((1 / 2 + η : ℝ) + (-t) * Complex.I)‖ := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hconj k t η (positive_of_mem (by linarith) hk) hη, norm_star]
  rw [hn]
  have hpos := hpositive K t η hK hη hη'
  have hneg := hpositive K (-t) η hK hη hη'
  simp only [scale_neg, Complex.ofReal_neg] at hneg
  linarith

end Cubic.BoxAsymptotic.AngularFirstMoment
