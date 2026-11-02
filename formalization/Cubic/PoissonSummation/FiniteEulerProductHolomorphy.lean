import Cubic.PoissonSummation.FiniteEulerProductConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Holomorphy of the finite transform's Euler expression

The existing locally uniform products converge on `Re z>1`. Each local
factor is holomorphic there, so mathlib's theorem on locally uniform limits
gives holomorphy of their product. This supplies the analytic input to the
upper-half-plane contour argument in `thm:heightZetaFunctionFormula2`.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteEulerProduct

theorem differentiableOn_splitFactor (p : SplitPrimes) :
    DifferentiableOn ℂ (splitFactor p) {z : ℂ | 1 < z.re} := by
  have hc : Differentiable ℂ (fun z : ℂ => (p.1 : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (.inl (by exact_mod_cast p.1.2.ne_zero))
  exact ((differentiable_const _).add ((differentiable_const _).mul hc)).differentiableOn.div
    (((differentiable_const _).sub hc).pow 2).differentiableOn
    (fun z hz => pow_ne_zero _ (Complex.one_sub_prime_cpow_ne_zero p.1.2 hz))

theorem differentiableOn_inertFactor (q : InertPrimes) :
    DifferentiableOn ℂ (inertFactor q) {z : ℂ | 1 < z.re} := by
  have hc : Differentiable ℂ (fun z : ℂ => (q.1 : ℂ) ^ (-(2 * z))) :=
    ((differentiable_const _).mul differentiable_id).neg.const_cpow
      (.inl (by exact_mod_cast q.1.2.ne_zero))
  apply ((differentiable_const _).sub hc).differentiableOn.inv
  intro z hz
  apply Complex.one_sub_prime_cpow_ne_zero q.1.2
  change 1 < z.re at hz
  norm_num [Complex.mul_re]
  linarith

/-- The finite transform expression is holomorphic, not just continuous, on its convergence domain. -/
theorem differentiableOn_value : DifferentiableOn ℂ value {z : ℂ | 1 < z.re} := by
  have hi : DifferentiableOn ℂ (fun z => ∏' q : InertPrimes, inertFactor q z)
      {z : ℂ | 1 < z.re} :=
    locally_uniform_inert.differentiableOn
      (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
        fun q _ => differentiableOn_inertFactor q)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hs : DifferentiableOn ℂ (fun z => ∏' p : SplitPrimes, splitFactor p z)
      {z : ℂ | 1 < z.re} :=
    locally_uniform_split.differentiableOn
      (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
        fun p _ => differentiableOn_splitFactor p)
      (isOpen_lt continuous_const Complex.continuous_re)
  exact ((differentiableOn_const _).mul hi).mul hs

/-- The complex continuation of the real spectral parameter, with the same sign. -/
def complexSpectralParameter (σ t : ℂ) : ℂ := σ - Real.pi * Complex.I * t

@[simp]
theorem complexSpectralParameter_ofReal (σ : ℂ) (t : ℝ) :
    complexSpectralParameter σ t = spectralParameter σ t := rfl

theorem complexSpectralParameter_re (σ t : ℂ) :
    (complexSpectralParameter σ t).re = σ.re + Real.pi * t.im := by
  simp [complexSpectralParameter, Complex.mul_re, Complex.mul_im]

theorem upper_half_plane_parameter (σ t : ℂ) (ht : 0 ≤ t.im) :
    σ.re ≤ (complexSpectralParameter σ t).re := by
  rw [complexSpectralParameter_re]
  exact le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le ht)

/-- Boundedness throughout the entire closed upper half-plane, rather than only the real line. -/
theorem upper_half_plane_bound (σ : ℂ) (hσ : 1 < σ.re) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℂ, 0 ≤ t.im → ‖value (complexSpectralParameter σ t)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := half_plane_bound σ.re hσ
  exact ⟨C, hC, fun t ht => hbound _ (upper_half_plane_parameter σ t ht)⟩

/-- The continuation is holomorphic at every point of the closed upper half-plane. -/
theorem differentiableAt_upper_half_plane (σ t : ℂ) (hσ : 1 < σ.re) (ht : 0 ≤ t.im) :
    DifferentiableAt ℂ (fun w => value (complexSpectralParameter σ w)) t := by
  have hz := hσ.trans_le (upper_half_plane_parameter σ t ht)
  have hf := differentiableOn_value.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  exact hf.comp t (by unfold complexSpectralParameter; fun_prop)

end Cubic.PoissonSummation.FiniteEulerProduct
