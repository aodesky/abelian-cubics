import Cubic.PoissonSummation.ArchimedeanFourier

/-!
# Integrable decay of the archimedean Fourier transform

For `Re(s₀)>0`, `Re(σ)>0`, the computed Fourier transform has a majorant
`C/(1+|t|)²`. The proof uses the combined numerator `s₀+2σ`; bounding the
two reciprocal terms separately would lose the integrable decay.
All statements concern the actual coordinate integral constructed in
`ArchimedeanFourier`, not a function defined to be the candidate formula.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanFourier

open MeasureTheory

/-- A vertical affine denominator with positive real part controls `1+|t|`. -/
private theorem affine_denominator_bound (z : ℂ) (b : ℝ) (hz : 0 < z.re) (hb : b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 + |t| ≤ C * ‖z + b * Complex.I * t‖ := by
  have hbpos : 0 < |b| := abs_pos.mpr hb
  refine ⟨(1 + ‖z‖ / z.re) / |b| + 1 / z.re, by positivity, ?_⟩
  intro t
  let d : ℂ := z + b * Complex.I * t
  have hreal : z.re ≤ ‖d‖ := by
    have h := Complex.re_le_norm d
    simpa [d] using h
  have hunit : 1 ≤ ‖d‖ / z.re := (le_div_iff₀ hz).mpr (by simpa using hreal)
  have hzscale : ‖z‖ ≤ (‖z‖ / z.re) * ‖d‖ := by
    calc
      ‖z‖ = (‖z‖ / z.re) * z.re := (div_mul_cancel₀ _ hz.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)
  have htri : |b| * |t| ≤ ‖d‖ + ‖z‖ := by
    calc
      |b| * |t| = ‖(b : ℂ) * Complex.I * t‖ := by simp
      _ = ‖d - z‖ := by congr 1; dsimp [d]; ring
      _ ≤ _ := norm_sub_le _ _
  have ht : |t| ≤ ((1 + ‖z‖ / z.re) / |b|) * ‖d‖ := by
    calc
      |t| ≤ (‖d‖ + ‖z‖) / |b| := (le_div_iff₀ hbpos).mpr (by simpa [mul_comm] using htri)
      _ ≤ (‖d‖ + (‖z‖ / z.re) * ‖d‖) / |b| := by gcongr
      _ = _ := by ring
  calc
    1 + |t| ≤ ‖d‖ / z.re + ((1 + ‖z‖ / z.re) / |b|) * ‖d‖ := add_le_add hunit ht
    _ = _ := by dsimp [d]; ring

/-- A global majorant, including bounded `t`, with the paper's quadratic decay. -/
theorem norm_fourier_le_quadratic (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖fourier s₀ σ t‖ ≤ C / (1 + |t|) ^ 2 := by
  obtain ⟨A, hA, hAb⟩ := affine_denominator_bound s₀ (2 * Real.pi) h₀ (by positivity)
  obtain ⟨B, hB, hBb⟩ := affine_denominator_bound (2 * σ) (-2 * Real.pi)
    (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hσ) (by positivity)
  refine ⟨‖s₀ + 2 * σ‖ * (A * B), by positivity, ?_⟩
  intro t
  have ha := hAb t
  have hb := hBb t
  have hap : 0 < ‖s₀ + 2 * Real.pi * Complex.I * t‖ :=
    norm_pos_iff.mpr (positive_denominator_ne_zero s₀ t h₀)
  have hbp : 0 < ‖2 * σ - 2 * Real.pi * Complex.I * t‖ :=
    norm_pos_iff.mpr (negative_denominator_ne_zero σ t hσ)
  have hb' : 1 + |t| ≤ B * ‖2 * σ - 2 * Real.pi * Complex.I * t‖ := by
    convert hb using 1; push_cast; congr 2; ring
  have ha' : 1 + |t| ≤ A * ‖s₀ + 2 * Real.pi * Complex.I * t‖ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using ha
  have hprod := mul_le_mul ha' hb' (by positivity : 0 ≤ 1 + |t|) (by positivity)
  rw [fourier_eq_fraction s₀ σ t h₀ hσ, norm_div, norm_mul]
  apply (div_le_div_iff₀ (mul_pos hap hbp) (by positivity : 0 < (1 + |t|) ^ 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (norm_nonneg (s₀ + 2 * σ))]

theorem continuous_fourier (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Continuous (fourier s₀ σ) := by
  have heq : fourier s₀ σ = fun t : ℝ => (s₀ + 2 * σ) /
      ((s₀ + 2 * Real.pi * Complex.I * t) * (2 * σ - 2 * Real.pi * Complex.I * t)) :=
    funext (fun t => fourier_eq_fraction s₀ σ t h₀ hσ)
  rw [heq]
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  exact mul_ne_zero (positive_denominator_ne_zero s₀ t h₀) (negative_denominator_ne_zero σ t hσ)

/-- Absolute integrability in the spectral variable, distinct from spatial integrability. -/
theorem integrable_fourier (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Integrable (fourier s₀ σ) := by
  obtain ⟨C, hC, hbound⟩ := norm_fourier_le_quadratic s₀ σ h₀ hσ
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_fourier s₀ σ h₀ hσ).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro t
  calc
    ‖fourier s₀ σ t‖ ≤ C / (1 + |t|) ^ 2 := hbound t
    _ ≤ C / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left hC (by positivity)
      nlinarith [abs_nonneg t, sq_abs t]
    _ = C * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

end Cubic.PoissonSummation.ArchimedeanFourier
