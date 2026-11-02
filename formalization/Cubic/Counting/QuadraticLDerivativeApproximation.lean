import Cubic.Counting.EulerKroneckerGammaReduction
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Finite derivative approximants and the Gamma-value limit

The corrected finite Dirichlet sums have an explicit derivative at zero.
Mathlib's proved Euler limit for `log Gamma` evaluates the limit of these
derivatives. The companion `QuadraticLApproximationIdentification` module
identifies this limit with the derivative of the L-function using locally
uniform convergence of holomorphic functions; pointwise convergence would not
suffice for this step.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLDerivativeApproximation

open Filter
open scoped Topology

/-- The tail correction allows continuation across `Re(s)=0`.
Its convergence to the L-function is proved in `QuadraticLApproximationIdentification`. -/
def approximation (n : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n + 2),
    ((3 * (k : ℂ) + 1) ^ (-s) - (3 * (k : ℂ) + 2) ^ (-s))) +
    (3 * ((n : ℂ) + 1)) ^ (-s) / 3

def derivativeApproximation (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 2),
    (Real.log (3 * (k : ℝ) + 2) - Real.log (3 * (k : ℝ) + 1))) -
    Real.log (3 * ((n : ℝ) + 1)) / 3

private theorem log_pair (k : ℕ) :
    Real.log (3 * (k : ℝ) + 2) - Real.log (3 * (k : ℝ) + 1) =
      Real.log ((2 / 3 : ℝ) + k) - Real.log ((1 / 3 : ℝ) + k) := by
  rw [show 3 * (k : ℝ) + 2 = 3 * ((2 / 3 : ℝ) + k) by ring,
    show 3 * (k : ℝ) + 1 = 3 * ((1 / 3 : ℝ) + k) by ring,
    Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  ring

theorem derivativeApproximation_eq_gammaSeq (n : ℕ) :
    derivativeApproximation n =
      Real.BohrMollerup.logGammaSeq (1 / 3) (n + 1) -
        Real.BohrMollerup.logGammaSeq (2 / 3) (n + 1) - Real.log 3 / 3 := by
  simp only [derivativeApproximation, log_pair, Real.BohrMollerup.logGammaSeq,
    Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd, Finset.sum_sub_distrib]
  rw [Real.log_mul (by norm_num) (by positivity)]
  ring

theorem derivativeApproximation_limit : Tendsto derivativeApproximation atTop
    (𝓝 (-Real.log 3 / 3 + Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)))) := by
  have h₁ := (Real.BohrMollerup.tendsto_log_gamma
    (by norm_num : (0 : ℝ) < 1 / 3)).comp (tendsto_add_atTop_nat 1)
  have h₂ := (Real.BohrMollerup.tendsto_log_gamma
    (by norm_num : (0 : ℝ) < 2 / 3)).comp (tendsto_add_atTop_nat 1)
  have h := (h₁.sub h₂).sub_const (Real.log 3 / 3)
  have he : Real.log (Real.Gamma (1 / 3)) - Real.log (Real.Gamma (2 / 3)) -
      Real.log 3 / 3 = -Real.log 3 / 3 + Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) := by
    rw [Real.log_div (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
      (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne']
    ring
  rw [he] at h
  simpa only [Function.comp_apply, ← derivativeApproximation_eq_gammaSeq] using h

private theorem inverse_power_derivative (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s : ℂ => (a : ℂ) ^ (-s)) (-(Real.log a : ℂ)) 0 := by
  convert (hasDerivAt_neg (0 : ℂ)).const_cpow
    (c := (a : ℂ)) (Or.inl (by exact_mod_cast ha.ne')) using 1
  simp
  exact Complex.ofReal_log ha.le

theorem approximation_derivative (n : ℕ) :
    deriv (approximation n) 0 = (derivativeApproximation n : ℂ) := by
  have hsum : HasDerivAt (fun s : ℂ => ∑ k ∈ Finset.range (n + 2),
      ((3 * (k : ℂ) + 1) ^ (-s) - (3 * (k : ℂ) + 2) ^ (-s)))
      (∑ k ∈ Finset.range (n + 2),
        ((Real.log (3 * (k : ℝ) + 2) - Real.log (3 * (k : ℝ) + 1) : ℝ) : ℂ)) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    convert (inverse_power_derivative (3 * (k : ℝ) + 1) (by positivity)).fun_sub
      (inverse_power_derivative (3 * (k : ℝ) + 2) (by positivity)) using 1 <;> push_cast <;> ring
  have htail := (inverse_power_derivative (3 * ((n : ℝ) + 1)) (by positivity)).div_const (3 : ℂ)
  have h := (hsum.fun_add htail).deriv
  simpa [approximation, derivativeApproximation, neg_div, sub_eq_add_neg] using h

/-- The finite derivatives have the required classical limit. Passing the
derivative through the limit is `zero_derivative_of_locally_uniform`. -/
theorem approximation_derivative_limit : Tendsto (fun n => deriv (approximation n) 0) atTop
    (𝓝 (-(Real.log 3 : ℂ) / 3 +
      (Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) : ℂ))) := by
  have h := Complex.continuous_ofReal.tendsto _ |>.comp derivativeApproximation_limit
  simpa only [approximation_derivative, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat] using h

theorem approximation_differentiable (n : ℕ) : Differentiable ℂ (approximation n) := by
  have h₁ (k : ℕ) : 3 * (k : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 3 * (k : ℝ) + 1 ≠ 0 by positivity)
  have h₂ (k : ℕ) : 3 * (k : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show 3 * (k : ℝ) + 2 ≠ 0 by positivity)
  have ht : 3 * ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 3 * ((n : ℝ) + 1) ≠ 0 by positivity)
  unfold approximation
  fun_prop (disch := first | exact Or.inl (h₁ _) | exact Or.inl (h₂ _) | exact Or.inl ht)

/-- The derivative at zero, given locally uniform convergence of the approximants
(proved in `QuadraticLApproximationIdentification`): derivatives of a locally
uniform limit of holomorphic functions converge. -/
theorem zero_derivative_of_locally_uniform
    (h : TendstoLocallyUniformlyOn approximation
      (DirichletCharacter.LFunction Cubic.PoissonSummation.QuadraticDirichletCharacter.character)
      atTop {s : ℂ | -1 < s.re}) :
    CubicTargets.Counting.QuadraticLZeroDerivative.Claim := by
  have hd := h.deriv (Eventually.of_forall fun n =>
    (approximation_differentiable n).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  have h₀ := hd.tendsto_at (show (0 : ℂ) ∈ {s : ℂ | -1 < s.re} by norm_num)
  exact tendsto_nhds_unique h₀ approximation_derivative_limit

end Cubic.Counting.QuadraticLDerivativeApproximation
