import Cubic.BoxAsymptotic.SmoothWrappedProfile
import Cubic.BoxAsymptotic.SmoothWeightCalculus
import Mathlib.Analysis.Normed.Group.Bounded

/-! The actual product weights used in the box-counting proof satisfy the
full smoothing lemma. Their normalized derivatives are rescaled fixed
profile derivatives, hence bounded independently of all three scale/center
parameters. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothProductWeight

open Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

def radialProfile (Φ : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv Φ x

theorem radial_smooth {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (radialProfile Φ) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hΦ).2

theorem radial_support {Φ : ℝ → ℝ} {a b : ℝ}
    (hs : Function.support Φ ⊆ Icc a b) : Function.support (radialProfile Φ) ⊆ Icc a b := by
  intro x hx
  apply closure_minimal hs isClosed_Icc
  apply support_deriv_subset
  intro hz
  exact hx (by simp [radialProfile, hz])

theorem radial_iterate_smooth {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : ℕ) :
    ContDiff ℝ ∞ (radialProfile^[j] Φ) := by
  induction j with
  | zero => exact hΦ
  | succ j ih => simpa only [Function.iterate_succ_apply'] using radial_smooth ih

theorem radial_iterate_support {Φ : ℝ → ℝ} {a b : ℝ}
    (hs : Function.support Φ ⊆ Icc a b) (j : ℕ) :
    Function.support (radialProfile^[j] Φ) ⊆ Icc a b := by
  induction j with
  | zero => exact hs
  | succ j ih => simpa only [Function.iterate_succ_apply'] using radial_support ih

theorem angular_iterate_support {Ψ : ℝ → ℝ}
    (hs : Function.support Ψ ⊆ Icc (-4) 4) (ℓ : ℕ) :
    Function.support (deriv^[ℓ] Ψ) ⊆ Icc (-4) 4 := by
  induction ℓ with
  | zero => exact hs
  | succ ℓ ih => simpa only [Function.iterate_succ_apply'] using SmoothWrappedProfile.deriv_support ih

theorem smooth {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hsΨ : Function.support Ψ ⊆ Icc (-4) 4) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => weight Φ Ψ X Θ θ₀ p.1 p.2) := by
  exact (hΦ.comp (contDiff_fst.div_const X)).mul
    ((SmoothWrappedProfile.smooth hΨ hsΨ hΘ hΘ').comp
      (contDiff_snd.sub contDiff_const))

theorem periodic (Φ Ψ : ℝ → ℝ) (X Θ θ₀ n θ : ℝ) :
    weight Φ Ψ X Θ θ₀ n (θ + 2 * Real.pi) = weight Φ Ψ X Θ θ₀ n θ := by
  unfold weight
  rw [show θ + 2 * Real.pi - θ₀ = (θ - θ₀) + 2 * Real.pi by ring]
  rw [wrap, toIocMod_add_right]
  rfl

theorem support {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hsΦ : Function.support Φ ⊆ Icc (1 / 2) 4)
    (hsΨ : Function.support Ψ ⊆ Icc (-4) 4) (hX : 0 < X) (hΘ : 0 < Θ) :
    Function.support (fun p : ℝ × ℝ => weight Φ Ψ X Θ θ₀ p.1 p.2) ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ} := by
  intro p hp
  have hΦ : Φ (p.1 / X) ≠ 0 := fun h => hp (by simp [weight, h])
  have hΨ : Ψ (wrap (p.2 - θ₀) / Θ) ≠ 0 := fun h => hp (by simp [weight, h])
  have hr := hsΦ hΦ
  have ha := hsΨ hΨ
  refine ⟨?_, (div_le_iff₀ hX).mp hr.2, ?_⟩
  · have := (le_div_iff₀ hX).mp hr.1
    linarith
  · have h := abs_le.mpr ha
    rw [abs_div, abs_of_pos hΘ, div_le_iff₀ hΘ] at h
    exact h

theorem angular_identity {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : Function.support Ψ ⊆ Icc (-4) 4)
    (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    angularDerivative Θ (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2) =
      (fun p => weight Φ (deriv Ψ) X Θ θ₀ p.1 p.2) := by
  funext p
  have hd := ((SmoothWrappedProfile.hasDerivAt hΨ hsΨ hΘ hΘ' (p.2 - θ₀)).comp p.2
    ((hasDerivAt_id p.2).sub_const θ₀)).const_mul (Φ (p.1 / X))
  simp only [Function.comp_def, id_eq, mul_one] at hd
  change Θ * deriv (fun θ => Φ (p.1 / X) * SmoothWrappedProfile.profile Ψ Θ (θ - θ₀)) p.2 = _
  rw [hd.deriv]
  dsimp [weight, SmoothWrappedProfile.profile]
  field_simp

theorem radial_identity {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    radialDerivative (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2) =
      (fun p => weight (radialProfile Φ) Ψ X Θ θ₀ p.1 p.2) := by
  funext p
  have hd := (((hΦ.differentiable (by simp)) (p.1 / X)).hasDerivAt.comp p.1
    ((hasDerivAt_id p.1).div_const X)).mul_const (Ψ (wrap (p.2 - θ₀) / Θ))
  simp only [Function.comp_def, id_eq] at hd
  change p.1 * deriv (fun n => Φ (n / X) * Ψ (wrap (p.2 - θ₀) / Θ)) p.1 = _
  rw [hd.deriv]
  dsimp [weight, radialProfile]
  ring

theorem angular_iterate {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : Function.support Ψ ⊆ Icc (-4) 4)
    (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) (ℓ : ℕ) :
    ((angularDerivative Θ)^[ℓ]) (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2) =
      (fun p => weight Φ (deriv^[ℓ] Ψ) X Θ θ₀ p.1 p.2) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [Function.iterate_succ_apply', ih, angular_identity
      (hΨ.iterate_deriv ℓ) (angular_iterate_support hsΨ ℓ) hΘ hΘ']
    rw [Function.iterate_succ_apply']

theorem radial_iterate {Φ Ψ : ℝ → ℝ} {X Θ θ₀ : ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (j : ℕ) :
    (radialDerivative^[j]) (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2) =
      (fun p => weight (radialProfile^[j] Φ) Ψ X Θ θ₀ p.1 p.2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, radial_identity (radial_iterate_smooth hΦ j)]
    rw [Function.iterate_succ_apply']

theorem bounded_profile {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hs : Function.support f ⊆ Icc a b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hz : f x = 0
  · simpa only [hz, abs_zero] using le_max_right C 0
  · have hh : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x (hs hz)
    exact hh.trans (le_max_left _ _)

theorem derivative_bound {Φ Ψ : ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hsΦ : Function.support Φ ⊆ Icc (1 / 2) 4)
    (hsΨ : Function.support Ψ ⊆ Icc (-4) 4) (J : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ X Θ θ₀ : ℝ, 0 < Θ → Θ ≤ 1 / 4 →
      normalizedDerivativeBound (fun p => weight Φ Ψ X Θ θ₀ p.1 p.2) Θ M J := by
  have hφ (j : ℕ) := bounded_profile (radial_iterate_smooth hΦ j).continuous
    (radial_iterate_support hsΦ j)
  have hψ (ℓ : ℕ) := bounded_profile (hΨ.iterate_deriv ℓ).continuous
    (angular_iterate_support hsΨ ℓ)
  choose B hB0 hB using hφ
  choose C hC0 hC using hψ
  let M := (∑ j ∈ Finset.range (J + 1), B j) * (∑ ℓ ∈ Finset.range (J + 1), C ℓ)
  have hBM := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (J + 1)) => hB0 i)
  have hCM := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (J + 1)) => hC0 i)
  refine ⟨M, mul_nonneg hBM hCM, fun X Θ θ₀ hΘ hΘ' j ℓ hjℓ p => ?_⟩
  rw [angular_iterate hΨ hsΨ hΘ hΘ', radial_iterate hΦ]
  change |(radialProfile^[j] Φ) (p.1 / X) * (deriv^[ℓ] Ψ) (wrap (p.2 - θ₀) / Θ)| ≤ M
  rw [abs_mul]
  have hj : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  have hℓ : ℓ ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  exact mul_le_mul ((hB j _).trans (Finset.single_le_sum (fun i _ => hB0 i) hj))
    ((hC ℓ _).trans (Finset.single_le_sum (fun i _ => hC0 i) hℓ)) (abs_nonneg _)
    (Finset.sum_nonneg (fun i _ => hB0 i))

end Cubic.BoxAsymptotic.SmoothProductWeight
