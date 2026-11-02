import Cubic.BoxAsymptotic.SmoothAngularTransform
import Cubic.Analysis.CompactMellinDerivative

/-! Repeated integration by parts in both variables of the test-weight
Fourier--Mellin transform. The multiplier for `x d/dx` is `-s`; that for
`Θ d/dθ` is `i k Θ`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothTransformDerivatives

open Set Complex MeasureTheory
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothAngularTransform
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.BoxAsymptotic.SmoothWeightCalculus
open scoped ContDiff

variable {w : ℝ × ℝ → ℝ} {a b : ℝ}

theorem coefficient_deriv_continuous (hw : ContDiff ℝ ∞ w) (k : ℤ) :
    Continuous (deriv (angularCoefficient w k)) := by
  let dw : ℝ × ℝ → ℝ := fun p => fderiv ℝ w p (1, 0)
  have hdw : ContDiff ℝ ∞ dw := (hw.fderiv_right (by simp)).clm_apply contDiff_const
  have he : deriv (angularCoefficient w k) = angularCoefficient dw k := by
    funext x
    exact (coefficient_hasDerivAt hw k x).deriv
  rw [he]
  exact angularCoefficient_continuous hdw.continuous k

theorem radial_identity (hw : ContDiff ℝ ∞ w) (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) (s : ℂ) :
    transform (radialDerivative w) k s = -s * transform w k s := by
  have he : angularCoefficient (radialDerivative w) k =
      fun x : ℝ => (x : ℂ) * deriv (angularCoefficient w k) x :=
    funext (coefficient_radialDerivative hw k)
  unfold transform
  rw [he]
  exact Cubic.Analysis.CompactMellin.radial_identity
    (fun x => (coefficient_hasDerivAt hw k x).differentiableAt)
    (coefficient_deriv_continuous hw k) ha hab (angularCoefficient_support hs k) s

theorem angular_iterate_identity (hw : ContDiff ℝ ∞ w)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (Θ : ℝ) (k : ℤ) (s : ℂ) (ℓ : ℕ) :
    transform ((angularDerivative Θ)^[ℓ] w) k s =
      ((Θ : ℂ) * (k : ℂ) * I) ^ ℓ * transform w k s := by
  have he : angularCoefficient ((angularDerivative Θ)^[ℓ] w) k =
      fun x => ((Θ : ℂ) * (k : ℂ) * I) ^ ℓ * angularCoefficient w k x :=
    funext (fun x => coefficient_angular_iterate hw hp Θ k x ℓ)
  unfold transform
  rw [he]
  exact mellin_const_smul (angularCoefficient w k) s (𝕜 := ℂ)
    (c := ((Θ : ℂ) * (k : ℂ) * I) ^ ℓ)

theorem radial_iterate_identity (hw : ContDiff ℝ ∞ w) (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) (s : ℂ) (j : ℕ) :
    transform (radialDerivative^[j] w) k s = (-s) ^ j * transform w k s := by
  have hclosed : IsClosed {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ b} :=
    isClosed_Icc.preimage continuous_fst
  induction j with
  | zero => simp
  | succ j ih =>
    have hh : ContDiff ℝ ∞ (radialDerivative^[j] w) := mixed_smooth hw 1 j 0
    have hhS : Function.support (radialDerivative^[j] w) ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b} :=
      mixed_support hw hclosed hs 1 j 0
    rw [Function.iterate_succ_apply', radial_identity hh ha hab hhS, ih, pow_succ]
    ring

theorem mixed_identity (hw : ContDiff ℝ ∞ w) (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b})
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (Θ : ℝ) (k : ℤ) (s : ℂ) (j ℓ : ℕ) :
    transform ((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) k s =
      (-s) ^ j * ((Θ : ℂ) * (k : ℂ) * I) ^ ℓ * transform w k s := by
  have hh : ContDiff ℝ ∞ ((angularDerivative Θ)^[ℓ] w) := mixed_smooth hw Θ 0 ℓ
  have hhS : Function.support ((angularDerivative Θ)^[ℓ] w) ⊆
      {p | a ≤ p.1 ∧ p.1 ≤ b} :=
    mixed_support hw (isClosed_Icc.preimage continuous_fst) hs Θ 0 ℓ
  rw [radial_iterate_identity hh ha hab hhS, angular_iterate_identity hw hp]
  ring

end Cubic.BoxAsymptotic.SmoothTransformDerivatives
