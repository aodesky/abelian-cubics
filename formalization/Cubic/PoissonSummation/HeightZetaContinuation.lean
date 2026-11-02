import Cubic.PoissonSummation.QuadraticDirichletCharacter
import Cubic.PoissonSummation.HeightZetaCorrectionProduct
import Cubic.PoissonSummation.RiemannZetaMeromorphy
import Mathlib.Analysis.Meromorphic.Basic

/-!
# The meromorphic function in the height-zeta continuation argument

Use the actual Riemann zeta function and quadratic Dirichlet L-function,
with the correction product holomorphic by locally uniform convergence.
This file proves meromorphy of that independently defined expression. Equality
with the original Euler product and height series is established separately.
It does not rename `ζ L` as a Dedekind zeta function without an ideal-counting comparison.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContinuation

open Filter
open scoped Topology

def value (z : ℂ) : ℂ :=
  ((1 - (3 : ℂ) ^ (-z)) * riemannZeta z *
    DirichletCharacter.LFunction QuadraticDirichletCharacter.character z) ^ 2 *
      HeightZetaCorrectionProduct.value z

/-- The entire completed zeta function and reciprocal gamma function in mathlib
give meromorphy of the ordinary zeta function, including its pole at one. -/
theorem meromorphicAt_riemannZeta (z : ℂ) (hz : 0 < z.re) : MeromorphicAt riemannZeta z :=
  RiemannZetaMeromorphy.meromorphicAt z hz

/-- Meromorphy on the entire claimed open half-plane, with no Euler-product
convergence required for the individual zeta or Dirichlet factors there. -/
theorem meromorphicOn_value :
    MeromorphicOn value {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  intro z hz
  change (1 / 2 : ℝ) < z.re at hz
  have hpower : Differentiable ℂ (fun w : ℂ => (3 : ℂ) ^ (-w)) :=
    differentiable_id.neg.const_cpow (.inl (by norm_num))
  have hthree := ((differentiable_const (1 : ℂ)).sub hpower).analyticAt z
  have hL := QuadraticDirichletCharacter.differentiable_LFunction.analyticAt z
  have hcor := HeightZetaCorrectionProduct.differentiableOn_value.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  exact (((hthree.meromorphicAt.fun_mul (meromorphicAt_riemannZeta z (by linarith))).fun_mul
    hL.meromorphicAt).fun_pow 2).fun_mul hcor.meromorphicAt

end Cubic.PoissonSummation.HeightZetaContinuation
