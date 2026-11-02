import Cubic.BoxAsymptotic.SmoothWeightCalculus
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Smooth periodic weights of compact radial support have bounded normalized
derivatives of every fixed order. These bounds need not be uniform in the
weight: they are used only to justify each contour shift, before applying the
finite derivative budget for the uniform error estimate. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothWeightBounded

open Set
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.BoxAsymptotic.SmoothWeightCalculus
open scoped ContDiff

theorem bounded {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hw : Continuous w)
    (hp : ∀ x θ, w (x, θ + 2 * Real.pi) = w (x, θ))
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, |w p| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hw.continuousOn : ContinuousOn w (Icc a b ×ˢ Icc 0 (2 * Real.pi)))
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  by_cases hz : w p = 0
  · simp only [hz, abs_zero]
    exact le_max_right _ _
  have hr := hs hz
  let θ := toIocMod Real.two_pi_pos 0 p.2
  have hθ : θ ∈ Icc 0 (2 * Real.pi) := by
    have h := toIocMod_mem_Ioc Real.two_pi_pos 0 p.2
    exact ⟨h.1.le, by simpa using h.2⟩
  have hper : Function.Periodic (fun u => w (p.1, u)) (2 * Real.pi) := hp p.1
  have he : w p = w (p.1, θ) := by
    have h := hper.zsmul (toIocDiv Real.two_pi_pos 0 p.2) θ
    change w (p.1, toIocMod Real.two_pi_pos 0 p.2 +
      toIocDiv Real.two_pi_pos 0 p.2 • (2 * Real.pi)) = w (p.1, θ) at h
    rw [toIocMod_add_toIocDiv_zsmul] at h
    exact h
  rw [he]
  have hbound : |w (p.1, θ)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (p.1, θ) ⟨hr, hθ⟩
  exact hbound.trans (le_max_left _ _)

theorem derivative_bounds {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x θ, w (x, θ + 2 * Real.pi) = w (x, θ))
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b})
    (Θ : ℝ) (J : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ normalizedDerivativeBound w Θ M J := by
  have hc : IsClosed {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ b} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)
  have hex : ∀ j ℓ : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ p,
      |((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) p| ≤ M :=
    fun j ℓ => bounded (mixed_smooth hw Θ j ℓ).continuous
      (mixed_periodic hp Θ j ℓ) (mixed_support hw hc hs Θ j ℓ)
  choose B hB0 hB using hex
  let M : ℝ := ∑ j ∈ Finset.range (J + 1), ∑ ℓ ∈ Finset.range (J + 1), B j ℓ
  refine ⟨M, Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun ℓ _ => hB0 j ℓ)), ?_⟩
  intro j ℓ hjℓ p
  refine (hB j ℓ p).trans ?_
  have hj : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  have hℓ : ℓ ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  exact (Finset.single_le_sum (fun m _ => hB0 j m) hℓ).trans
    (Finset.single_le_sum (fun n _ => Finset.sum_nonneg (fun m _ => hB0 n m)) hj)

end Cubic.BoxAsymptotic.SmoothWeightBounded
