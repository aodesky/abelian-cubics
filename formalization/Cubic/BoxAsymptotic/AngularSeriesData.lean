import Cubic.BoxAsymptotic.ZeroModeMass
import Cubic.BoxAsymptotic.EisensteinCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The actual angular Fourier coefficients and Dirichlet series

These definitions use the original congruence-defined measure. In particular the
nonzero modes are not defined by the Euler products proposed in `eq:Dk` or `eq:Fk`.
The angular character has the paper's positive sign, `exp(i k θ)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSeriesData

open Complex CubicTargets.BoxAsymptotic

/-- The positive angular character `exp(i k θ)`. -/
def character (k : ℤ) (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * I) ^ k

/-- The character evaluated on the argument of a complex number. -/
def phase (k : ℤ) (z : ℂ) : ℂ := character k (Complex.arg z)

/-- The complex extension of the actual angular measure. -/
def muIntegralC (n : ℕ) (g : ℝ → ℂ) : ℂ :=
  (1 / 6 : ℂ) * ∑ᶠ β ∈ admissible n, g (Complex.arg (eis β))

/-- `∫ exp(i k θ) dμ_n(θ)`. -/
def coefficient (k : ℤ) (n : ℕ) : ℂ := muIntegralC n (character k)

/-- `F_k(s)`, initially interpreted in its half-plane of absolute convergence. -/
def series (k : ℤ) (s : ℂ) : ℂ := LSeries (coefficient k) s

theorem character_eq_exp (k : ℤ) (θ : ℝ) :
    character k θ = Complex.exp ((k : ℂ) * θ * I) := by
  rw [character, ← Complex.exp_int_mul]
  congr 1
  ring

@[simp] theorem character_zero (θ : ℝ) : character 0 θ = 1 := by simp [character]

@[simp] theorem norm_character (k : ℤ) (θ : ℝ) : ‖character k θ‖ = 1 := by
  simp [character, norm_zpow, Complex.norm_exp_ofReal_mul_I]

@[simp] theorem norm_phase (k : ℤ) (z : ℂ) : ‖phase k z‖ = 1 := norm_character _ _

theorem phase_eq_div (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    phase k z = (z / (‖z‖ : ℂ)) ^ k := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have he : Complex.exp ((Complex.arg z : ℂ) * I) = z / (‖z‖ : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa [mul_comm] using Complex.norm_mul_exp_arg_mul_I z
  exact congrArg (fun w : ℂ => w ^ k) he

theorem phase_mul (k : ℤ) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    phase k (z * w) = phase k z * phase k w := by
  rw [phase_eq_div k (mul_ne_zero hz hw), phase_eq_div k hz, phase_eq_div k hw,
    norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]

theorem phase_ofReal_pos (k : ℤ) {r : ℝ} (hr : 0 < r) : phase k r = 1 := by
  simp [phase, character, Complex.arg_ofReal_of_nonneg hr.le]

theorem phase_neg (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    phase k (-z) = (-1 : ℂ) ^ k * phase k z := by
  rw [phase_eq_div k (neg_ne_zero.mpr hz), phase_eq_div k hz, norm_neg,
    neg_div, neg_eq_neg_one_mul, mul_zpow]

theorem phase_neg_index (k : ℤ) (z : ℂ) :
    phase (-k) z = star (phase k z) := by
  rw [phase, phase, character, character, zpow_neg]
  exact Complex.inv_eq_conj (by simp [norm_zpow, Complex.norm_exp_ofReal_mul_I])

theorem muIntegralC_real (n : ℕ) (g : ℝ → ℝ) :
    muIntegralC n (fun θ => (g θ : ℂ)) = (muIntegral n g : ℂ) := by
  classical
  rw [muIntegralC, muIntegral,
    finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n),
    finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n)]
  push_cast
  rfl

theorem coefficient_zero (n : ℕ) : coefficient 0 n = (ZeroModeData.mass n : ℂ) := by
  simpa only [coefficient, character_zero, ZeroModeData.mass] using
    muIntegralC_real n (fun _ => 1)

theorem mass_nonneg (n : ℕ) : 0 ≤ ZeroModeData.mass n := by
  rw [ZeroModeMass.mass_eq]
  positivity

/-- Domination by the zero mode, uniformly in the angular frequency. -/
theorem norm_coefficient_le (k : ℤ) (n : ℕ) :
    ‖coefficient k n‖ ≤ ZeroModeData.mass n := by
  classical
  rw [coefficient, muIntegralC,
    finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n), norm_mul]
  calc
    _ ≤ ‖(1 / 6 : ℂ)‖ * ∑ β ∈ (ZeroModeMass.admissible_finite n).toFinset,
        ‖character k (Complex.arg (eis β))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ZeroModeData.mass n := by
      simp [ZeroModeMass.mass_eq, Set.ncard_eq_toFinset_card _
        (ZeroModeMass.admissible_finite n), div_eq_mul_inv, mul_comm]

theorem coefficient_neg_index (k : ℤ) (n : ℕ) :
    coefficient (-k) n = star (coefficient k n) := by
  classical
  simp only [coefficient, muIntegralC,
    finsum_mem_eq_finite_toFinset_sum _ (ZeroModeMass.admissible_finite n)]
  change (1 / 6 : ℂ) * ∑ β ∈ (ZeroModeMass.admissible_finite n).toFinset,
      phase (-k) (eis β) = _
  simp_rw [phase_neg_index]
  simp [phase]

end Cubic.BoxAsymptotic.AngularSeriesData
