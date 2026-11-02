import Cubic.BoxAsymptotic.SmoothWeightData
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Smoothness, support, and periodicity of the actual normalized differential
operators appearing in `lem:smooth`. In particular repeated integration by
parts does not change the radial support or angular period. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothWeightCalculus

open Set
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

variable {w : ℝ × ℝ → ℝ}

theorem radial_eq_fderiv (hw : Differentiable ℝ w) (p : ℝ × ℝ) :
    radialDerivative w p = p.1 * fderiv ℝ w p (1, 0) := by
  have h := (hw p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact congrArg (fun z => p.1 * z) h.deriv

theorem angular_eq_fderiv (hw : Differentiable ℝ w) (Θ : ℝ) (p : ℝ × ℝ) :
    angularDerivative Θ w p = Θ * fderiv ℝ w p (0, 1) := by
  have h := (hw p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact congrArg (fun z => Θ * z) h.deriv

theorem radial_smooth (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (radialDerivative w) := by
  have he : radialDerivative w = fun p => p.1 * fderiv ℝ w p (1, 0) :=
    funext (radial_eq_fderiv (hw.differentiable (by simp)))
  rw [he]
  exact contDiff_fst.mul ((hw.fderiv_right (by simp)).clm_apply contDiff_const)

theorem angular_smooth (hw : ContDiff ℝ ∞ w) (Θ : ℝ) :
    ContDiff ℝ ∞ (angularDerivative Θ w) := by
  have he : angularDerivative Θ w = fun p => Θ * fderiv ℝ w p (0, 1) :=
    funext (angular_eq_fderiv (hw.differentiable (by simp)) Θ)
  rw [he]
  exact contDiff_const.mul ((hw.fderiv_right (by simp)).clm_apply contDiff_const)

theorem radial_support (hw : Differentiable ℝ w) {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) (hs : Function.support w ⊆ S) :
    Function.support (radialDerivative w) ⊆ S := by
  intro p hp
  apply closure_minimal hs hS
  apply support_fderiv_subset ℝ
  intro he
  apply hp
  rw [radial_eq_fderiv hw, he]
  simp

theorem angular_support (hw : Differentiable ℝ w) {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) (hs : Function.support w ⊆ S) (Θ : ℝ) :
    Function.support (angularDerivative Θ w) ⊆ S := by
  intro p hp
  apply closure_minimal hs hS
  apply support_fderiv_subset ℝ
  intro he
  apply hp
  rw [angular_eq_fderiv hw, he]
  simp

theorem radial_periodic {P : ℝ} (hw : ∀ n θ, w (n, θ + P) = w (n, θ)) :
    ∀ n θ, radialDerivative w (n, θ + P) = radialDerivative w (n, θ) := by
  intro n θ
  simp only [radialDerivative, hw]

theorem angular_periodic {P : ℝ} (hw : ∀ n θ, w (n, θ + P) = w (n, θ)) (Θ : ℝ) :
    ∀ n θ, angularDerivative Θ w (n, θ + P) = angularDerivative Θ w (n, θ) := by
  intro n θ
  have h : (fun y => w (n, y + P)) = fun y => w (n, y) := funext (hw n)
  simp only [angularDerivative]
  rw [← deriv_comp_add_const (fun y => w (n, y)) P θ, h]

theorem mixed_smooth (hw : ContDiff ℝ ∞ w) (Θ : ℝ) (j ℓ : ℕ) :
    ContDiff ℝ ∞ ((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) := by
  have hℓ : ∀ ℓ, ContDiff ℝ ∞ ((angularDerivative Θ)^[ℓ] w) := by
    intro ℓ
    induction ℓ with
    | zero => exact hw
    | succ ℓ ih =>
      simpa only [Function.iterate_succ_apply'] using angular_smooth ih Θ
  induction j with
  | zero => exact hℓ ℓ
  | succ j ih => simpa only [Function.iterate_succ_apply'] using radial_smooth ih

theorem mixed_periodic {P : ℝ} (hw : ∀ n θ, w (n, θ + P) = w (n, θ))
    (Θ : ℝ) (j ℓ : ℕ) :
    ∀ n θ, ((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) (n, θ + P) =
      ((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) (n, θ) := by
  have hℓ : ∀ ℓ, ∀ n θ, ((angularDerivative Θ)^[ℓ] w) (n, θ + P) =
      ((angularDerivative Θ)^[ℓ] w) (n, θ) := by
    intro ℓ
    induction ℓ with
    | zero => exact hw
    | succ ℓ ih =>
      simpa only [Function.iterate_succ_apply'] using angular_periodic ih Θ
  induction j with
  | zero => exact hℓ ℓ
  | succ j ih => simpa only [Function.iterate_succ_apply'] using radial_periodic ih

theorem mixed_support (hw : ContDiff ℝ ∞ w) {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) (hs : Function.support w ⊆ S) (Θ : ℝ) (j ℓ : ℕ) :
    Function.support ((radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w)) ⊆ S := by
  have hℓ : ∀ ℓ, Function.support ((angularDerivative Θ)^[ℓ] w) ⊆ S := by
    intro ℓ
    induction ℓ with
    | zero => exact hs
    | succ ℓ ih =>
      have hh : ContDiff ℝ ∞ ((angularDerivative Θ)^[ℓ] w) := mixed_smooth hw Θ 0 ℓ
      simpa only [Function.iterate_succ_apply'] using
        angular_support (hh.differentiable (by simp)) hS ih Θ
  induction j with
  | zero => exact hℓ ℓ
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using
      radial_support ((mixed_smooth hw Θ j ℓ).differentiable (by simp)) hS ih

end Cubic.BoxAsymptotic.SmoothWeightCalculus
