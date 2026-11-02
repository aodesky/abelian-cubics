import Cubic.PoissonSummation.QuadraticDirichletCharacter
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Regularizing the quadratic `ζ L` expression at 1

Mathlib provides the entire regularization of `(u-1)ζ(u)` and the
nonvanishing of the actual nontrivial Dirichlet `L(1,χ)`. Their product
gives the regularized numerator for the paper's Laurent calculation.

The function `value` is explicitly named as a `ζ L` expression. This module
does not identify it with the ideal-counting Dedekind zeta function, or
identify its regularized logarithmic derivative with the paper's `γ_E`.
Those arithmetic comparisons are established where the corresponding paper result is assembled (`prop:leadingTerms`).
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticZetaRegularization

open Filter DirichletCharacter
open scoped Topology

def value (u : ℂ) : ℂ :=
  riemannZeta u * LFunction QuadraticDirichletCharacter.character u

def regular (u : ℂ) : ℂ :=
  LFunctionTrivChar₁ 1 u * LFunction QuadraticDirichletCharacter.character u

theorem differentiable_regular : Differentiable ℂ regular :=
  (differentiable_LFunctionTrivChar₁ 1).mul QuadraticDirichletCharacter.differentiable_LFunction

theorem regular_one : regular 1 = LFunction QuadraticDirichletCharacter.character 1 := by
  simp [regular, LFunctionTrivChar₁]

theorem regular_one_ne_zero : regular 1 ≠ 0 := by
  rw [regular_one]
  exact LFunction_apply_one_ne_zero QuadraticDirichletCharacter.character_ne_one

theorem regular_eq (u : ℂ) (hu : u ≠ 1) : regular u = (u - 1) * value u := by
  simp only [regular, LFunctionTrivChar₁, Function.update_of_ne hu,
    LFunctionTrivChar, LFunction_modOne_eq, value]
  ring

theorem differentiableAt_value (u : ℂ) (hu : u ≠ 1) : DifferentiableAt ℂ value u :=
  (differentiableAt_riemannZeta hu).mul
    (QuadraticDirichletCharacter.differentiable_LFunction u)

theorem residue_limit : Tendsto (fun u : ℂ => (u - 1) * value u)
    (𝓝[≠] (1 : ℂ)) (𝓝 (LFunction QuadraticDirichletCharacter.character 1)) := by
  have h : Tendsto regular (𝓝[≠] (1 : ℂ)) (𝓝 (regular 1)) :=
    (differentiable_regular.continuous.continuousAt (x := (1 : ℂ))).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [regular_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact regular_eq u hu

theorem log_derivative_identity (u : ℂ) (hu : u ≠ 1) (hr : regular u ≠ 0) :
    deriv value u / value u + 1 / (u - 1) = deriv regular u / regular u := by
  have he : regular =ᶠ[𝓝 u] (fun w : ℂ => (w - 1) * value w) := by
    filter_upwards [isOpen_ne.mem_nhds hu]
      with w hw using regular_eq w hw
  have hn : value u ≠ 0 := by
    rw [regular_eq u hu] at hr
    exact (mul_ne_zero_iff.mp hr).2
  rw [he.deriv_eq, (((hasDerivAt_id' u).sub_const 1).fun_mul
    (differentiableAt_value u hu).hasDerivAt).deriv, regular_eq u hu]
  field_simp [sub_ne_zero.mpr hu]
  ring

/-- The defining logarithmic-derivative limit for the `ζ L` expression.
Its identification with the paper's Euler–Kronecker constant still requires
the genuine Dedekind-zeta comparison. -/
theorem log_derivative_limit : Tendsto
    (fun u : ℂ => deriv value u / value u + 1 / (u - 1))
    (𝓝[≠] (1 : ℂ)) (𝓝 (deriv regular 1 / regular 1)) := by
  have hc := differentiable_regular.continuous.continuousAt (x := (1 : ℂ))
  have hd := (differentiable_regular.contDiff.continuous_deriv le_rfl).continuousAt
    (x := (1 : ℂ))
  have h : Tendsto (fun u : ℂ => deriv regular u / regular u)
      (𝓝[≠] (1 : ℂ)) (𝓝 (deriv regular 1 / regular 1)) :=
    (hd.div hc regular_one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hc.eventually_ne regular_one_ne_zero)] with u hu hr
  exact (log_derivative_identity u hu hr).symm

end Cubic.PoissonSummation.QuadraticZetaRegularization
