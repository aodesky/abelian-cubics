import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute convergence justifies pairing a Dirichlet series with a vertically
integrable Mellin transform, term by term, on its initial line of convergence. -/

noncomputable section

namespace Cubic.Analysis.MellinDirichletPairing

open Complex MeasureTheory

/-- The normalized integral on the upwards vertical line `Re s = σ`. -/
def pairing (σ : ℝ) (F H : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, F (σ + t * I) * H (σ + t * I)

theorem norm_term_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ : ℂ) + t * I) n‖ = ‖LSeries.term a σ n‖ := by
  simp [LSeries.norm_term_eq]

theorem continuous_term_vertical (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((σ : ℂ) + t * I) n) := by
  by_cases hn : n = 0
  · simpa only [hn, LSeries.term_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · simp only [LSeries.term_of_ne_zero hn, div_eq_mul_inv]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    apply continuous_const.mul
    apply Continuous.inv₀
    · exact (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + t * I)).const_cpow (Or.inl hn')
    · intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn')

theorem term_integrable {H : ℂ → ℂ} {σ : ℝ}
    (hH : VerticalIntegrable H σ) (a : ℕ → ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + t * I) n *
      H (σ + t * I)) := by
  refine (hH.norm.const_mul ‖LSeries.term a σ n‖).mono'
    ((continuous_term_vertical a σ n).aestronglyMeasurable.mul hH.1) ?_
  filter_upwards [] with t
  simp only [norm_mul, norm_term_vertical, le_refl]

theorem term_pairing (a : ℕ → ℂ) (H : ℂ → ℂ) (σ : ℝ) (n : ℕ) :
    pairing σ (fun s => LSeries.term a s n) H =
      if n = 0 then 0 else a n * mellinInv σ H n := by
  by_cases hn : n = 0
  · simp [hn, pairing]
  rw [if_neg hn, pairing, mellinInv]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [mul_left_comm (a n)]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg]
  simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_assoc]

theorem hasSum_pairing {a : ℕ → ℂ} {H : ℂ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a σ) (hH : VerticalIntegrable H σ) :
    HasSum (fun n : ℕ => if n = 0 then 0 else a n * mellinInv σ H n)
      (pairing σ (LSeries a) H) := by
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + t * I) n * H (σ + t * I)‖) := by
    simp_rw [norm_mul, norm_term_vertical, integral_const_mul]
    exact ha.norm.mul_right _
  have h := (hasSum_integral_of_summable_integral_norm
    (term_integrable hH a) hsum).const_smul (1 / (2 * Real.pi) : ℝ)
  have hi : (fun t : ℝ => ∑' n : ℕ,
      LSeries.term a ((σ : ℂ) + t * I) n * H (σ + t * I)) =
      (fun t : ℝ => LSeries a (σ + t * I) * H (σ + t * I)) := by
    ext t
    exact tsum_mul_right
  rw [hi] at h
  simpa only [← term_pairing, pairing] using h

end Cubic.Analysis.MellinDirichletPairing
