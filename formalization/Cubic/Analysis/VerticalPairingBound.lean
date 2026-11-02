import Cubic.Analysis.MellinDirichletPairing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Bounding a finite sum of normalized vertical integrals by an integrable
quadratic-decay majorant. Integrability of each summand is established before
the finite sum is exchanged with the integral. -/

noncomputable section

namespace Cubic.Analysis.VerticalPairingBound

open MeasureTheory Complex
open Cubic.Analysis.MellinDirichletPairing

theorem finite_sum {ι : Type*} (S : Finset ι) (F H : ι → ℂ → ℂ) (σ : ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (hc : ∀ k ∈ S, Continuous (fun t : ℝ => F k (σ + t * I) * H k (σ + t * I)))
    (hb : ∀ t : ℝ, (∑ k ∈ S, ‖F k (σ + t * I) * H k (σ + t * I)‖) ≤
      B / (1 + |t|) ^ 2) :
    (∑ k ∈ S, ‖pairing σ (F k) (H k)‖) ≤ B := by
  have hdom (t : ℝ) : B / (1 + |t|) ^ 2 ≤ B * (1 + t ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left hB (by positivity)
    nlinarith [abs_nonneg t, sq_abs t]
  have hi : ∀ k ∈ S, Integrable
      (fun t : ℝ => F k (σ + t * I) * H k (σ + t * I)) := by
    intro k hk
    apply (integrable_inv_one_add_sq.const_mul B).mono' (hc k hk).aestronglyMeasurable
    filter_upwards [] with t
    exact (Finset.single_le_sum
      (fun j _ => norm_nonneg (F j (σ + t * I) * H j (σ + t * I))) hk).trans
        ((hb t).trans (hdom t))
  have hbint : (∫ t : ℝ, ∑ k ∈ S, ‖F k (σ + t * I) * H k (σ + t * I)‖) ≤
      B * Real.pi := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => Finset.sum_nonneg (fun k _ => norm_nonneg _)))
      (integrable_inv_one_add_sq.const_mul B)
      (Filter.Eventually.of_forall (fun t => (hb t).trans (hdom t)))
    simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h
  have hnormal : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  simp only [pairing, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnormal]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∑ k ∈ S,
        ∫ t : ℝ, ‖F k (σ + t * I) * H k (σ + t * I)‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => norm_integral_le_integral_norm _)) hnormal
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, ∑ k ∈ S,
        ‖F k (σ + t * I) * H k (σ + t * I)‖ := by
      rw [integral_finset_sum S (fun k hk => (hi k hk).norm)]
    _ ≤ (1 / (2 * Real.pi)) * (B * Real.pi) := mul_le_mul_of_nonneg_left hbint hnormal
    _ = B / 2 := by field_simp
    _ ≤ B := by linarith

end Cubic.Analysis.VerticalPairingBound
