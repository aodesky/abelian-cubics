import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Laurent coefficients from an analytic numerator

Supporting analytic machinery for `prop:leadingTerms`: if a function is
`A(s)/(s-a)²` near `a`, the first two coefficients are `A(a)` and `A'(a)`.
The remainder is bounded on a punctured complex neighborhood. A nonzero
numerator at `a` makes the pole order exactly two.
-/

noncomputable section

namespace Cubic.PoissonSummation.AnalyticLaurent

open Filter Asymptotics
open scoped Topology

theorem quadratic_remainder {A : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ A a) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R a ∧ ∀ᶠ s in 𝓝 a,
      A s = A a + deriv A a * (s - a) + (s - a) ^ 2 * R s := by
  have hA0 : AnalyticAt ℂ A (a + 0) := by simpa using hA
  have hshift : AnalyticAt ℂ (fun u : ℂ => A (a + u)) 0 :=
    hA0.comp (show AnalyticAt ℂ (fun u : ℂ => a + u) 0 by fun_prop)
  obtain ⟨R, hR, he⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul 2
  have hd : deriv (fun u : ℂ => A (a + u)) 0 = deriv A a := by
    have ht := hA0.differentiableAt.hasDerivAt.comp 0 ((hasDerivAt_id' 0).const_add a)
    simpa using ht.deriv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedDeriv_zero, iteratedDeriv_one, pow_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, pow_one, smul_eq_mul, one_mul,
    add_zero, hd] at he
  have hz : Tendsto (fun s : ℂ => s - a) (𝓝 a) (𝓝 0) := by
    simpa using (continuous_id.sub (continuous_const : Continuous (fun _ : ℂ => a))).tendsto a
  refine ⟨fun s => R (s - a), ?_, ?_⟩
  · have hR0 : AnalyticAt ℂ R (a - a) := by simpa using hR
    exact hR0.comp (f := fun s : ℂ => s - a) (by fun_prop)
  · filter_upwards [hz.eventually he] with s hs
    simpa only [add_sub_cancel, mul_comm (s - a) (deriv A a)] using hs

theorem laurent_of_analytic_numerator {A F : ℂ → ℂ} {a : ℂ}
    (hA : AnalyticAt ℂ A a)
    (hF : F =ᶠ[𝓝[≠] a] (fun s => A s / (s - a) ^ 2)) :
    (fun s => F s - A a / (s - a) ^ 2 - deriv A a / (s - a))
      =O[𝓝[≠] a] (fun _ => (1 : ℂ)) := by
  obtain ⟨R, hR, he⟩ := quadratic_remainder hA
  have hc : Tendsto R (𝓝[≠] a) (𝓝 (R a)) :=
    hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hrem : (fun s => F s - A a / (s - a) ^ 2 - deriv A a / (s - a)) =ᶠ[𝓝[≠] a] R := by
    filter_upwards [hF, nhdsWithin_le_nhds he, self_mem_nhdsWithin] with s hs he hsne
    rw [hs, he]
    field_simp [sub_ne_zero.mpr hsne]
    ring
  exact (hc.isBigO_one ℂ).congr' hrem.symm EventuallyEq.rfl

theorem order_of_nonzero_numerator {A F : ℂ → ℂ} {a : ℂ}
    (hA : AnalyticAt ℂ A a) (hne : A a ≠ 0)
    (hF : F =ᶠ[𝓝[≠] a] (fun s => A s / (s - a) ^ 2)) :
    meromorphicOrderAt F a = (-2 : ℤ) := by
  have hm : MeromorphicAt F a :=
    (hA.meromorphicAt.fun_div
      (((MeromorphicAt.id a).fun_sub (MeromorphicAt.const a a)).fun_pow 2)).congr hF.symm
  apply (meromorphicOrderAt_eq_int_iff hm).mpr
  refine ⟨A, hA, hne, ?_⟩
  filter_upwards [hF] with s hs
  rw [hs]
  norm_num [zpow_neg, smul_eq_mul, div_eq_mul_inv, mul_comm]
  left
  norm_cast

end Cubic.PoissonSummation.AnalyticLaurent
