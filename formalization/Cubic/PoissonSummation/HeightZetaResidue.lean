import Cubic.PoissonSummation.HeightZetaFormulaData
import Cubic.PoissonSummation.FiniteEulerProductHolomorphy
import Cubic.PoissonSummation.AdelicSpectralIntegrand

/-!
# The poles and residue in the height-zeta contour argument

Continue the already evaluated local transforms in the spectral variable.
The upper pole is `-s₀/(2πi)`; evaluating the finite parameter there gives
`z=s₀/2+σ`. The residue below retains the finite factor `1/6`: the separate
Poisson scalar six cancels it only after contour integration.
No contour-closing or Poisson equality is asserted by these local calculations.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaResidue

open Filter FiniteEulerProduct HeightZetaFormulaData
open scoped Topology

def upperPole (s₀ : ℂ) : ℂ := -s₀ / (2 * Real.pi * Complex.I)

def lowerPole (σ : ℂ) : ℂ := σ / (Real.pi * Complex.I)

def archimedeanContinuation (s₀ σ t : ℂ) : ℂ :=
  (s₀ + 2 * σ) / ((s₀ + 2 * Real.pi * Complex.I * t) *
    (2 * σ - 2 * Real.pi * Complex.I * t))

def fullContinuation (s₀ σ t : ℂ) : ℂ :=
  archimedeanContinuation s₀ σ t * value (complexSpectralParameter σ t)

theorem upperPole_eq (s₀ : ℂ) :
    upperPole s₀ = s₀ * Complex.I / (2 * Real.pi) := by
  unfold upperPole
  field_simp
  ring_nf
  simp

theorem lowerPole_eq (σ : ℂ) : lowerPole σ = -σ * Complex.I / Real.pi := by
  unfold lowerPole
  field_simp
  ring_nf
  simp

theorem upperPole_im (s₀ : ℂ) : (upperPole s₀).im = s₀.re / (2 * Real.pi) := by
  rw [upperPole_eq]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.mul_I_im] using
    (Complex.div_ofReal_im (s₀ * Complex.I) (2 * Real.pi))

theorem lowerPole_im (σ : ℂ) : (lowerPole σ).im = -σ.re / Real.pi := by
  rw [lowerPole_eq]
  simp [Complex.div_ofReal_im]

theorem upperPole_pos (s₀ : ℂ) (h₀ : 0 < s₀.re) : 0 < (upperPole s₀).im := by
  rw [upperPole_im]
  exact div_pos h₀ (mul_pos (by norm_num) Real.pi_pos)

theorem lowerPole_neg (σ : ℂ) (hσ : 0 < σ.re) : (lowerPole σ).im < 0 := by
  rw [lowerPole_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hσ) Real.pi_pos

theorem parameter_at_upperPole (s₀ σ : ℂ) :
    complexSpectralParameter σ (upperPole s₀) = parameter s₀ σ := by
  unfold complexSpectralParameter upperPole parameter
  field_simp
  ring

/-- On the real line this rational continuation is the actual coordinate Fourier integral. -/
theorem archimedeanContinuation_ofReal (s₀ σ : ℂ) (t : ℝ)
    (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    archimedeanContinuation s₀ σ t = ArchimedeanFourier.fourier s₀ σ t := by
  exact (ArchimedeanFourier.fourier_eq_fraction s₀ σ t h₀ hσ).symm

/-- The complex continuation restricts to the original local Haar integrals. -/
theorem fullContinuation_ofReal (s₀ σ : ℂ) (t : ℝ)
    (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    fullContinuation s₀ σ t = AdelicSpectralIntegrand.integrand s₀ σ t := by
  rw [fullContinuation, archimedeanContinuation_ofReal s₀ σ t h₀ (lt_trans zero_lt_one hσ),
    complexSpectralParameter_ofReal, AdelicSpectralIntegrand.integrand_eq_coordinate s₀ σ t h₀ hσ,
    LocalModelProduct.finiteFourier_claim.spectral_product s₀ σ t hσ]

private theorem frequencyScale_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

theorem first_denominator (s₀ t : ℂ) :
    s₀ + 2 * Real.pi * Complex.I * t =
      (2 * Real.pi * Complex.I) * (t - upperPole s₀) := by
  unfold upperPole
  field_simp
  ring

theorem second_denominator_at_upperPole (s₀ σ : ℂ) :
    2 * σ - 2 * Real.pi * Complex.I * upperPole s₀ = s₀ + 2 * σ := by
  unfold upperPole
  field_simp
  ring

theorem second_denominator (σ t : ℂ) :
    2 * σ - 2 * Real.pi * Complex.I * t =
      -(2 * Real.pi * Complex.I) * (t - lowerPole σ) := by
  unfold lowerPole
  field_simp
  ring

theorem upperPole_ne_lowerPole (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    upperPole s₀ ≠ lowerPole σ := by
  intro he
  have h := upperPole_pos s₀ h₀
  rw [he] at h
  exact (lowerPole_neg σ hσ).asymm h

/-- The upper pole is the only possible singularity in the closed upper half-plane. -/
theorem differentiableAt_fullContinuation (s₀ σ t : ℂ) (hσ : 1 < σ.re)
    (ht : 0 ≤ t.im) (hne : t ≠ upperPole s₀) :
    DifferentiableAt ℂ (fullContinuation s₀ σ) t := by
  have hlower : t ≠ lowerPole σ := by
    intro he
    rw [he] at ht
    exact (lowerPole_neg σ (lt_trans zero_lt_one hσ)).not_ge ht
  have hd : (s₀ + 2 * Real.pi * Complex.I * t) *
      (2 * σ - 2 * Real.pi * Complex.I * t) ≠ 0 := by
    rw [first_denominator, second_denominator]
    exact mul_ne_zero (mul_ne_zero frequencyScale_ne_zero (sub_ne_zero.mpr hne))
      (mul_ne_zero (neg_ne_zero.mpr frequencyScale_ne_zero) (sub_ne_zero.mpr hlower))
  have ha : DifferentiableAt ℂ (archimedeanContinuation s₀ σ) t := by
    unfold archimedeanContinuation
    exact (differentiableAt_const _).div (by fun_prop) hd
  exact ha.mul (differentiableAt_upper_half_plane σ t hσ ht)

/-- Cancel only on the punctured neighborhood; totalized division at the pole
must not be mistaken for a removable-singularity value. -/
theorem cancel_upperPole (s₀ σ t : ℂ) (ht : t ≠ upperPole s₀) :
    (t - upperPole s₀) * archimedeanContinuation s₀ σ t =
      (s₀ + 2 * σ) /
        ((2 * Real.pi * Complex.I) * (2 * σ - 2 * Real.pi * Complex.I * t)) := by
  rw [archimedeanContinuation, first_denominator]
  have ht' : t - upperPole s₀ ≠ 0 := sub_ne_zero.mpr ht
  by_cases hd : 2 * σ - 2 * Real.pi * Complex.I * t = 0
  · simp [hd]
  · field_simp [ht', frequencyScale_ne_zero, hd]

/-- The exact residue coefficient of the archimedean rational function. -/
theorem archimedean_residue (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Tendsto (fun t => (t - upperPole s₀) * archimedeanContinuation s₀ σ t)
      (𝓝[≠] upperPole s₀) (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹)) := by
  have hn : s₀ + 2 * σ ≠ 0 := by
    have hr : 0 < (s₀ + 2 * σ).re := by
      norm_num [Complex.mul_re]
      linarith
    intro he
    simp [he] at hr
  have hcont : ContinuousAt (fun t : ℂ => (s₀ + 2 * σ) /
      ((2 * Real.pi * Complex.I) * (2 * σ - 2 * Real.pi * Complex.I * t))) (upperPole s₀) := by
    apply continuousAt_const.div (by fun_prop)
    rw [second_denominator_at_upperPole]
    exact mul_ne_zero frequencyScale_ne_zero hn
  have hv : (s₀ + 2 * σ) /
      ((2 * Real.pi * Complex.I) * (2 * σ - 2 * Real.pi * Complex.I * upperPole s₀)) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ := by
    rw [second_denominator_at_upperPole]
    field_simp
  have hlimit := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds (s := {upperPole s₀}ᶜ))
  rw [hv] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (cancel_upperPole s₀ σ t ht).symm

/-- The residue of the product with the finite transform, with all signs and the
local factor at three still present. -/
theorem full_residue (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Tendsto (fun t => (t - upperPole s₀) * fullContinuation s₀ σ t)
      (𝓝[≠] upperPole s₀)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ * value (parameter s₀ σ))) := by
  have hf := (differentiableAt_upper_half_plane σ (upperPole s₀) hσ
    (upperPole_pos s₀ h₀).le).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {upperPole s₀}ᶜ))
  rw [parameter_at_upperPole] at hf
  simpa only [fullContinuation, mul_assoc] using
    (archimedean_residue s₀ σ h₀ (lt_trans zero_lt_one hσ)).mul hf

end Cubic.PoissonSummation.HeightZetaResidue
