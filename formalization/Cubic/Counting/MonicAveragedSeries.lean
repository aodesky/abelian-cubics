import Cubic.Counting.MonicEulerFactor
import Cubic.PoissonSummation.LeadingTerms

/-!
# Proof of `eqn:monicAveragedSeries`

The first equality is the identity `1/3 + 3^{-z}(1 + 2·3^{-z})/(3(1 - 3^{-z}))
= (1 + 2·3^{-2z})/(3(1 - 3^{-z}))`. For the second, the Euler product of the height zeta
function (through `prop:leadingTerms`, which rests on `thm:heightZetaFunctionFormula`)
gives `Z₀(s) = ζ_E(s/2)² E(s)` for `Re s > 2`, and
`(1 + 2·3^{-2z})/(3(1 - 3^{-z})) · E(2z) = 𝓔_mon(z)` (`MonicEulerFactor.eq_correction`).

The only hypothesis is the Poisson summation input used by `prop:leadingTerms`.
-/

noncomputable section

namespace Cubic.Counting.MonicAveragedSeries

open Cubic.Counting.MonicConstantsData Cubic.Counting.MonicEulerFactor Cubic.PoissonSummation

theorem trace_average {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    1 / 3 + (3 : ℂ) ^ (-z) * (1 + 2 * (3 : ℂ) ^ (-z)) / (3 * (1 - (3 : ℂ) ^ (-z))) =
      (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 - (3 : ℂ) ^ (-z))) := by
  have h := three_sub_ne_zero hz
  rw [three_sq]
  field_simp
  ring

theorem «eqn:monicAveragedSeries»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.Counting.GeneralMonic.MonicAveragedSeriesClaim := by
  obtain ⟨D, F, γ, c₂, c₁, h⟩ := leadingTerms_expansion hPoisson
  intro z hz
  have hz' : (1 / 2 : ℝ) < z.re := by linarith
  have h2 : 2 < (2 * z).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hne : 2 * z ≠ 2 := fun he => by rw [he] at h2; norm_num at h2
  refine ⟨by rw [trace_average hz'], ?_⟩
  rw [← h.continuation_agrees (2 * z) h2, h.factorization (2 * z) (by linarith) hne, half_two,
    h.dedekind_agrees z hz, eq_correction hz']
  ring

end Cubic.Counting.MonicAveragedSeries
