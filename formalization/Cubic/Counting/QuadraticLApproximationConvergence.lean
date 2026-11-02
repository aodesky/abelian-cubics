import Cubic.Counting.QuadraticLIncrementBound
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic convergence of the corrected quadratic Dirichlet sums

The second-derivative increment estimate gives uniform convergence on every
compact subset of `Re(s) > -1`. This is the convergence needed to differentiate
at zero, rather than merely a pointwise continuation formula.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLApproximationConvergence

open Filter Set QuadraticLDerivativeApproximation QuadraticLIncrementBound
open scoped Topology

def limit (s : ℂ) : ℂ := approximation 0 s +
  ∑' n : ℕ, (approximation (n + 1) s - approximation n s)

theorem telescoping (N : ℕ) (s : ℂ) : approximation 0 s +
    ∑ n ∈ Finset.range N, (approximation (n + 1) s - approximation n s) =
      approximation N s := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; ring

theorem locally_uniform : TendstoLocallyUniformlyOn approximation limit atTop
    {s : ℂ | -1 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro K hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀, hmin⟩ := hcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₁, _, hmax⟩ := hcompact.exists_isMaxOn hne
    (show ContinuousOn (fun s : ℂ => ‖s * (s + 1)‖) K by fun_prop)
  have hsum := tendstoUniformlyOn_tsum_nat
    (summable_majorant s₀.re ‖s₁ * (s₁ + 1)‖ (hK hs₀))
    (fun n s hs => increment_bound n s s₀.re ‖s₁ * (s₁ + 1)‖
      (hK hs₀) (hmin hs) (hmax hs))
  have hconst : TendstoUniformlyOn (fun _ : ℕ => approximation 0) (approximation 0)
      atTop K := by
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n s hs => by
      simpa using hε
  have h := hconst.add hsum
  change TendstoUniformlyOn (fun n s => approximation 0 s +
    ∑ k ∈ Finset.range n, (approximation (k + 1) s - approximation k s)) limit atTop K at h
  simpa only [telescoping] using h

theorem limit_differentiableOn : DifferentiableOn ℂ limit {s : ℂ | -1 < s.re} :=
  locally_uniform.differentiableOn
    (Eventually.of_forall fun n => (approximation_differentiable n).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

end Cubic.Counting.QuadraticLApproximationConvergence
