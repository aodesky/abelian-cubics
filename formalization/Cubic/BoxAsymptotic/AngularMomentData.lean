import Cubic.BoxAsymptotic.AngularIdealData
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The functions and sums in `lem:moment`

The Hecke coefficients are sums of the actual primary ideal characters over
ideals of the indicated norm.  Analytic realizations must agree with these
Dirichlet series, and with the original angular Fourier series, on `Re s > 1`.
They are not defined by the proposed Euler factorization or a moment estimate.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularMomentData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData
open scoped BigOperators

/-- The coefficient of `L^(3)(s, ψ_k)` at the positive integer `n`. -/
def heckeCoefficient (k : ℤ) (n : ℕ) : ℂ :=
  ∑ᶠ I ∈ {I : Ideal Integers | Ideal.absNorm I = n}, psi k I

/-- The Hecke Dirichlet series, used only in its convergent half-plane. -/
def heckeSeries (k : ℤ) (s : ℂ) : ℂ := LSeries (heckeCoefficient k) s

/-- Positive integer frequencies in the real interval `(K,2K]`. -/
def positiveModes (K : ℝ) : Finset ℤ := Finset.Ioc ⌊K⌋ ⌊2 * K⌋

/-- The even positive frequencies used for the second moment. -/
def evenModes (K : ℝ) : Finset ℤ := (positiveModes K).filter (fun k => Even k)

/-- Both signs of the frequencies in `(K,2K]`. -/
def signedModes (K : ℝ) : Finset ℤ :=
  positiveModes K ∪ (positiveModes K).image (fun k => -k)

/-- The common polynomial and logarithmic factor in the two estimates. -/
def momentScale (A : ℕ) (K t : ℝ) : ℝ :=
  K * (1 + |t|) ^ A * (Real.log (2 * K + 2 * |t|)) ^ A

/-- Agreement with the actual series and the domains of holomorphy needed by
the moment lemma. No bound, functional equation, or Euler identity is included.
Only nonzero frequencies occur in the lemma; its Hecke moment uses only even
frequencies. The angular moment still uses every nonzero frequency. -/
structure AnalyticRealization (L F : ℤ → ℂ → ℂ) : Prop where
  hecke_entire : ∀ k, Even k → k ≠ 0 → Differentiable ℂ (L k)
  hecke_eq : ∀ k, Even k → k ≠ 0 → ∀ s, 1 < s.re → L k s = heckeSeries k s
  angular_holomorphic : ∀ k, k ≠ 0 →
    DifferentiableOn ℂ (F k) {s : ℂ | 1 / 2 < s.re}
  angular_eq : ∀ k, k ≠ 0 → ∀ s, 1 < s.re →
    F k s = AngularSeriesData.series k s

/-- Both conclusions of `lem:moment`, with constants uniform in all displayed
parameters. Increasing the absolute exponent permits a nonnegative integer. -/
def MomentBounds (L F : ℤ → ℂ → ℂ) : Prop :=
  ∃ (A : ℕ) (C : ℝ), 0 < C ∧
    (∀ (K t σ : ℝ), 2 ≤ K → 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      (∑ k ∈ evenModes K, ‖L k (σ + t * Complex.I)‖ ^ 2) ≤
        C * momentScale A K t) ∧
    (∀ (K t η : ℝ), 2 ≤ K → 0 < η → η ≤ 1 / 4 →
      (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * Complex.I)‖) ≤
        C * η⁻¹ ^ 4 * momentScale A K t)

end Cubic.BoxAsymptotic.AngularMomentData
