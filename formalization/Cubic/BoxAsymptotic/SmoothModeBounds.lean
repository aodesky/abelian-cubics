import Cubic.BoxAsymptotic.SmoothShiftedExpansion
import Cubic.BoxAsymptotic.AngularContinuation
import Cubic.BoxAsymptotic.AngularMomentSums
import CubicTargets.BoxAsymptotic.AngularMoment

/-! The first-moment bound for the chosen continuations and the uniform
polynomial bound for the five frequencies `|k| ≤ 2`. The latter includes the
zero mode on the shifted line, which stays a fixed distance from its pole. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothModeBounds

open Complex
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothShiftedExpansion
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums

theorem mode_holomorphic (hHecke : PrimitiveHecke.BlackBox) (k : ℤ) :
    DifferentiableOn ℂ (mode hHecke k) ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
  by_cases hk : k = 0
  · simpa only [mode, if_pos hk] using ZeroModeStripGrowth.holomorphic
  · simpa only [mode, if_neg hk] using
      (HeckeAnalyticRealization.angular_holomorphic hHecke hk).mono (fun _ hs => hs.1)

theorem continuous_on_left (hHecke : PrimitiveHecke.BlackBox) (k : ℤ)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    Continuous (fun t : ℝ => mode hHecke k ((1 / 2 + η : ℝ) + t * I)) := by
  apply (mode_holomorphic hHecke k).continuousOn.comp_continuous (by fun_prop)
  intro t
  refine ⟨by simp; linarith, ?_⟩
  intro he
  have h := congrArg Complex.re he
  simp at h
  linarith

theorem growth_on_left (hHecke : PrimitiveHecke.BlackBox) (k : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ t : ℝ,
      ‖mode hHecke k ((1 / 2 + η : ℝ) + t * I)‖ ≤ C * η⁻¹ ^ 4 * (1 + |t|) ^ N := by
  by_cases hk : k = 0
  · obtain ⟨C, hC, hg⟩ := ZeroModeStripGrowth.growth
    refine ⟨C, hC, 8, fun η hη hη' t => ?_⟩
    have hd : 1 / 4 ≤ ‖((1 / 2 + η : ℝ) : ℂ) + t * I - 1‖ := by
      refine le_trans ?_ ((neg_le_abs ((((1 / 2 + η : ℝ) : ℂ) + t * I - 1).re)).trans
        (Complex.abs_re_le_norm _))
      simp
      linarith
    simpa only [mode, if_pos hk, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      hg η hη hη' (((1 / 2 + η : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith) hd
  · obtain ⟨C, hC, N, hg⟩ := AngularStripGrowth.angular_growth hHecke k hk
    refine ⟨C, hC, N, fun η hη hη' t => ?_⟩
    simpa only [mode, if_neg hk, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      hg η hη hη' (((1 / 2 + η : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith)

theorem small_growth (hHecke : PrimitiveHecke.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ t : ℝ,
      (∑ k ∈ Finset.Icc (-2 : ℤ) 2, ‖mode hHecke k ((1 / 2 + η : ℝ) + t * I)‖) ≤
        C * η⁻¹ ^ 4 * (1 + |t|) ^ N := by
  choose B hB N hN using growth_on_left hHecke
  let S := Finset.Icc (-2 : ℤ) 2
  let C : ℝ := ∑ k ∈ S, B k
  let J : ℕ := ∑ k ∈ S, N k
  have hC : 0 < C := Finset.sum_pos (fun k _ => hB k) ⟨0, by simp [S]⟩
  refine ⟨C, hC, J, fun η hη hη' t => ?_⟩
  calc
    _ ≤ ∑ k ∈ S, B k * η⁻¹ ^ 4 * (1 + |t|) ^ J := by
      apply Finset.sum_le_sum
      intro k hk
      refine (hN k η hη hη' t).trans ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hB k).le (by positivity))
      exact pow_le_pow_right₀ (by linarith [abs_nonneg t])
        (Finset.single_le_sum (fun m _ => Nat.zero_le (N m)) hk)
    _ = _ := by simp only [C, Finset.sum_mul]

theorem first_moment (hHecke : PrimitiveHecke.BlackBox)
    (hmoment : AngularMomentClaim) :
    ∃ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ K t η : ℝ, 2 ≤ K → 0 < η → η ≤ 1 / 4 →
      (∑ k ∈ signedModes K, ‖mode hHecke k ((1 / 2 + η : ℝ) + t * I)‖) ≤
        C * η⁻¹ ^ 4 * momentScale A K t := by
  obtain ⟨L, F, hreal, A, C, hC, _, hfirst⟩ := hmoment
  have hcanonical := HeckeAnalyticRealization.realization hHecke
  refine ⟨A, C, hC, fun K t η hK hη hη' => ?_⟩
  convert hfirst K t η hK hη hη' using 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by
    have h := ((mem_signedModes (by linarith : 0 ≤ K)).mp hk).1
    intro he
    simp [he] at h
    linarith
  rw [mode, if_neg hk0]
  exact congrArg norm (AngularContinuation.angular_unique hcanonical hreal hk0 (by simp; linarith))

end Cubic.BoxAsymptotic.SmoothModeBounds
