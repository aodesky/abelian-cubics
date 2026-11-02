import Cubic.BoxAsymptotic.WeightedIdealBlocks
import Cubic.BoxAsymptotic.HeckeWeightVariation

/-! A uniform bound for each actual dyadic block, allowing the weight to
depend on the frequency. The hypotheses are pointwise weight control and
the separately proved maximal estimate, not an assumed moment conclusion. -/

noncomputable section

namespace Cubic.BoxAsymptotic.WeightedBlockBound

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.WeightedIdealSums
open Cubic.BoxAsymptotic.WeightedIdealBlocks Cubic.BoxAsymptotic.HeckeWeightVariation
open MeasureTheory

structure Control (w : ℝ → ℂ) (Q C : ℝ) : Prop where
  differentiable : DifferentiableOn ℝ w (Set.Ioi 0)
  continuous_deriv : ContinuousOn (deriv w) (Set.Ioi 0)
  small : ∀ x > 0, ‖w x - 1‖ ≤ C * (x / Q) ^ (1 / 4 : ℝ)
  small_deriv : ∀ x > 0, x * ‖deriv w x‖ ≤ C * (x / Q) ^ (1 / 4 : ℝ)
  large : ∀ x > 0, ‖w x‖ ≤ C * (Q / x) ^ 3
  large_deriv : ∀ x > 0, x * ‖deriv w x‖ ≤ C * (Q / x) ^ 3

theorem Control.on_interval {w : ℝ → ℂ} {Q C a b : ℝ} (h : Control w Q C) (ha : 0 < a) :
    (∀ x ∈ Set.Icc a b, DifferentiableAt ℝ w x) ∧ IntegrableOn (deriv w) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => ha.trans_le hx.1
  exact ⟨fun x hx => (h.differentiable x (hsub hx)).differentiableAt (isOpen_Ioi.mem_nhds (hsub hx)),
    (h.continuous_deriv.mono hsub).integrableOn_Icc⟩

def variationConstant (C : ℝ) : ℝ := 648 * (1 + C)

theorem variationConstant_pos {C : ℝ} (hC : 0 ≤ C) : 0 < variationConstant C := by
  unfold variationConstant
  positivity

theorem mean_bound {ι : Type*} (S : Finset ι) (χ : ι → Ideal Integers → ℂ)
    (a : Ideal Integers → ℂ) (w : ι → ℝ → ℂ) (Q : ι → ℝ)
    {Y C R : ℝ} (hY : 2 ≤ Y) (hC : 0 ≤ C)
    (hQ : ∀ k ∈ S, Y ≤ Q k ∧ Q k ≤ 3 * Y)
    (hw : ∀ k ∈ S, Control (w k) (Q k) C) (j : ℕ)
    (hmax : (∑ k ∈ S, maximal (χ k) a ((2 : ℝ) ^ j * Y) ^ 2) ≤ R) :
    (∑ k ∈ S, ‖block (χ k) a Y (w k) j‖ ^ 2) ≤
      (variationConstant C * (1 / 8 : ℝ) ^ j) ^ 2 * R := by
  cases j with
  | zero =>
    simp only [block, pow_zero, one_mul, mul_one] at hmax ⊢
    apply WeightedAngularSieve.initial_bound S χ a w
      (fun k hk => ((hw k hk).on_interval (by norm_num : (0 : ℝ) < 1)).1)
      (fun k hk => ((hw k hk).on_interval (by norm_num : (0 : ℝ) < 1)).2) ?_ hmax
    intro k hk
    have hv := initial_variation (by linarith : 1 ≤ Y) (hQ k hk).1 hC
      ((hw k hk).on_interval (by norm_num : (0 : ℝ) < 1)).2
      ((hw k hk).small Y (by linarith))
      (fun x hx => (hw k hk).small_deriv x (by linarith [hx.1]))
    exact hv.trans (by unfold variationConstant; linarith)
  | succ j =>
    have he : (2 : ℝ) ^ (j + 1) * Y / 2 = (2 : ℝ) ^ j * Y := by rw [pow_succ]; ring
    have hX : 0 < (2 : ℝ) ^ j * Y := by positivity
    have hXY : (2 : ℝ) ^ j * Y ≤ 2 ^ (j + 1) * Y := by rw [pow_succ]; nlinarith
    simp only [block]
    apply WeightedAngularSieve.interval_bound S χ a w hX.le hXY
      (fun k hk => ((hw k hk).on_interval hX).1)
      (fun k hk => ((hw k hk).on_interval hX).2) ?_ hmax
    intro k hk
    have hv := dyadic_variation (j + 1) (by linarith : 0 < Y)
      (by linarith [(hQ k hk).1] : 0 ≤ Q k) (hQ k hk).2 hC
      (by rw [he]; exact ((hw k hk).on_interval hX).2)
      (hw k hk).large (hw k hk).large_deriv
    rw [he] at hv
    exact hv.trans (by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold variationConstant
      linarith)

end Cubic.BoxAsymptotic.WeightedBlockBound
