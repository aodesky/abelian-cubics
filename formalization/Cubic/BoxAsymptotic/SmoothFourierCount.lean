import Cubic.BoxAsymptotic.SmoothFourierInversion

/-! Fourier reconstruction inside the original finite angular counting
measures. The arithmetic coefficients retain their positive Fourier sign. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothFourierCount

open Complex
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

def modeSum (w : ℝ × ℝ → ℝ) (N : ℕ) (k : ℤ) : ℂ :=
  ∑ n ∈ Finset.range N, coefficient k n * angularCoefficient w k n

theorem at_norm {w : ℝ × ℝ → ℝ}
    (hw : Continuous w)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (n : ℕ) (hs : Summable (fun k : ℤ => angularCoefficient w k n)) :
    HasSum (fun k : ℤ => coefficient k n * angularCoefficient w k n)
      (muIntegral n (fun θ => w (n, θ)) : ℂ) := by
  classical
  let S := (ZeroModeMass.admissible_finite n).toFinset
  have h := hasSum_sum (s := S) (fun β _ =>
    SmoothFourierInversion.reconstruction hw hp n (Complex.arg (eis β)) hs)
  have h' := h.mul_left (1 / 6 : ℂ)
  rw [← muIntegralC_real]
  convert h' using 1
  · ext k
    simp only [coefficient, muIntegralC,
      finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n),
      Finset.sum_mul, Finset.mul_sum, S]
    apply Finset.sum_congr rfl
    intro β _
    ring
  · simp only [muIntegralC,
      finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n), S]

theorem reconstruction {w : ℝ × ℝ → ℝ} {Θ M : ℝ}
    (hw : ContDiff ℝ ∞ w) (hΘ : 0 < Θ)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hb : normalizedDerivativeBound w Θ M 2) (N : ℕ) :
    HasSum (modeSum w N)
      ((∑ n ∈ Finset.range N, muIntegral n (fun θ => w (n, θ)) : ℝ) : ℂ) := by
  have h := hasSum_sum (s := Finset.range N) (fun n _ =>
    at_norm hw.continuous hp n
      (SmoothFourierInversion.coefficient_summable hw hΘ hp hb n))
  simpa only [modeSum, Complex.ofReal_sum] using h

end Cubic.BoxAsymptotic.SmoothFourierCount
