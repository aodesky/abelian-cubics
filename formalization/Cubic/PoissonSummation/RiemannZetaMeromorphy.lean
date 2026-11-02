import Cubic.PoissonSummation.QuadraticDirichletCharacter
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphy of the actual Riemann zeta function

This supporting fact is independent of the height continuation and its
Euler products. It can therefore be used in constructing their boundary
continuations without a circular dependency.
-/

noncomputable section

namespace Cubic.PoissonSummation.RiemannZetaMeromorphy

open Filter
open scoped Topology

theorem meromorphicAt (z : ℂ) (hz : 0 < z.re) : MeromorphicAt riemannZeta z := by
  have hΛ : MeromorphicAt completedRiemannZeta z := by
    change MeromorphicAt (fun w => completedRiemannZeta w) z
    simp_rw [completedRiemannZeta_eq]
    exact ((differentiable_completedZeta₀.analyticAt z).meromorphicAt.fun_sub
      ((MeromorphicAt.const (1 : ℂ) z).fun_div (MeromorphicAt.id z))).fun_sub
        ((MeromorphicAt.const (1 : ℂ) z).fun_div
          ((MeromorphicAt.const (1 : ℂ) z).fun_sub (MeromorphicAt.id z)))
  have hΓ := (Complex.differentiable_Gammaℝ_inv.analyticAt z).meromorphicAt
  apply (hΛ.fun_mul hΓ).congr
  have hU : {w : ℂ | 0 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  filter_upwards [nhdsWithin_le_nhds hU] with w hw
  have hw0 : w ≠ 0 := by
    intro he
    simp [he] at hw
  rw [riemannZeta_def_of_ne_zero hw0, div_eq_mul_inv]

end Cubic.PoissonSummation.RiemannZetaMeromorphy
