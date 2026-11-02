import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrals `I` and `J` of `thm:generalMonicCount`

`I = ∫_{-1}^{1} (3 + u²) du = 20/3` and
`J = ∫_{-1}^{1} (3 + u²) log(3 + u²) du = (40/3) log 2 + 4π√3/3 - 76/9`.
For `J`, an antiderivative of `(3 + u²) log(3 + u²)` is
`(u³/3 + 3u) log(3 + u²) - 2u³/9 - 4u + 4√3 arctan(u/√3)`.
We also record the Lipschitz constants and bounds of the two integrands on `[-2, 2]`
used for the Riemann sums.
-/

noncomputable section

namespace Cubic.Counting.GeneralMonicIntegrals

open Real intervalIntegral

/-- `3 + u²`. -/
def g₁ (u : ℝ) : ℝ := 3 + u ^ 2

/-- `(3 + u²) log(3 + u²)`. -/
def g₂ (u : ℝ) : ℝ := (3 + u ^ 2) * Real.log (3 + u ^ 2)

theorem g₁_pos (u : ℝ) : 0 < g₁ u := by unfold g₁; positivity

theorem continuous_g₁ : Continuous g₁ := by unfold g₁; fun_prop

theorem continuous_g₂ : Continuous g₂ := by
  unfold g₂
  exact (continuous_const.add (continuous_pow 2)).mul
    ((continuous_const.add (continuous_pow 2)).log fun u => (g₁_pos u).ne')

theorem integral_g₁ : ∫ u in (-1 : ℝ)..1, g₁ u = 20 / 3 := by
  simp only [g₁]
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const
    ((continuous_pow 2).intervalIntegrable _ _)]
  simp [integral_pow]; norm_num

/-- The antiderivative of `g₂`. -/
def F (u : ℝ) : ℝ :=
  (u ^ 3 / 3 + 3 * u) * Real.log (3 + u ^ 2) - 2 * u ^ 3 / 9 - 4 * u +
    4 * √3 * Real.arctan (u / √3)

theorem hasDerivAt_F (u : ℝ) : HasDerivAt F (g₂ u) u := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √3 := by positivity
  have hpos : 0 < 3 + u ^ 2 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u ^ 3 / 3 + 3 * u) (u ^ 2 + 3) u := by
    have := ((hasDerivAt_pow 3 u).div_const 3).add ((hasDerivAt_id u).const_mul 3)
    convert this using 1; simp
  have h2 : HasDerivAt (fun u : ℝ => Real.log (3 + u ^ 2)) (2 * u / (3 + u ^ 2)) u := by
    have := ((hasDerivAt_pow 2 u).const_add 3).log hpos.ne'
    convert this using 1; simp
  have h4 : HasDerivAt (fun u : ℝ => Real.arctan (u / √3)) (√3 / (3 + u ^ 2)) u := by
    have := (Real.hasDerivAt_arctan (u / √3)).comp u ((hasDerivAt_id u).div_const √3)
    convert this using 1
    field_simp
    rw [h3]
  have := ((((h1.mul h2).sub ((hasDerivAt_pow 3 u).const_mul (2 : ℝ) |>.div_const 9)).sub
    ((hasDerivAt_id u).const_mul 4)).add (h4.const_mul (4 * √3)))
  convert this using 1
  simp only [g₂]
  field_simp
  rw [h3]
  ring

theorem integral_g₂ :
    ∫ u in (-1 : ℝ)..1, g₂ u = 40 / 3 * Real.log 2 + 4 * π * √3 / 3 - 76 / 9 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_F u)
    (continuous_g₂.intervalIntegrable _ _)]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : Real.arctan (1 / √3) = π / 6 := by rw [one_div, Real.arctan_inv_sqrt_three]
  have ha' : Real.arctan (-1 / √3) = -(π / 6) := by
    rw [neg_div, Real.arctan_neg, ha]
  have hl : Real.log (3 + 1 ^ 2 : ℝ) = 2 * Real.log 2 := by
    rw [show (3 + 1 ^ 2 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl' : Real.log (3 + (-1) ^ 2 : ℝ) = 2 * Real.log 2 := by
    rw [show (3 + (-1) ^ 2 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [F, hl, hl', ha, ha']
  ring_nf

/-! ### Lipschitz constants and bounds on `[-2, 2]` -/

theorem abs_sq_sub_sq {x y : ℝ} (hx : x ∈ Set.Icc (-2 : ℝ) 2) (hy : y ∈ Set.Icc (-2 : ℝ) 2) :
    |x ^ 2 - y ^ 2| ≤ 4 * |x - y| := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem lip_g₁ : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2,
    |g₁ x - g₁ y| ≤ 4 * |x - y| := fun x hx y hy => by
  simp only [g₁, add_sub_add_left_eq_sub]; exact abs_sq_sub_sq hx hy

theorem bound_g₁ : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g₁ x| ≤ 7 := fun x hx => by
  rw [abs_of_pos (g₁_pos x), g₁]; nlinarith [hx.1, hx.2]

theorem log_le_six {a : ℝ} (h0 : 0 < a) (h : a ≤ 7) : Real.log a ≤ 6 := by
  linarith [Real.log_le_sub_one_of_pos h0]

theorem abs_log_sub_log {a b : ℝ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / 3 := by
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < a) (by linarith : 0 < b))
    rw [sub_div, div_self (by linarith : b ≠ 0)]; exact this
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < b) (by linarith : 0 < a))
    rw [sub_div, div_self (by linarith : a ≠ 0)]; exact this
  rw [abs_le]
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (by linarith)]
    constructor
    · have : (b - a) / a ≤ (b - a) / 3 := div_le_div_of_nonneg_left (by linarith) (by norm_num) ha
      linarith
    · have : (a - b) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have : 0 ≤ -(a - b) / 3 := by linarith
      linarith
  · rw [abs_of_nonneg (by linarith)]
    constructor
    · have : (b - a) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have : 0 ≤ (a - b) / 3 := by linarith
      linarith
    · have : (a - b) / b ≤ (a - b) / 3 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hb
      linarith

theorem lip_g₂ : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2,
    |g₂ x - g₂ y| ≤ 34 * |x - y| := fun x hx y hy => by
  have hxy := abs_sq_sub_sq hx hy
  set a := 3 + x ^ 2
  set b := 3 + y ^ 2
  have ha : 3 ≤ a := by simp only [a]; nlinarith
  have hb : 3 ≤ b := by simp only [b]; nlinarith
  have ha7 : a ≤ 7 := by simp only [a]; nlinarith [hx.1, hx.2]
  have hb7 : b ≤ 7 := by simp only [b]; nlinarith [hy.1, hy.2]
  have hab : |a - b| ≤ 4 * |x - y| := by
    simp only [a, b, add_sub_add_left_eq_sub]; exact hxy
  have hla := log_le_six (by linarith) ha7
  have hla0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hlog := abs_log_sub_log ha hb
  have e : g₂ x - g₂ y = (a - b) * Real.log a + b * (Real.log a - Real.log b) := by
    simp only [g₂, a, b]; ring
  rw [e]
  calc _ ≤ |(a - b) * Real.log a| + |b * (Real.log a - Real.log b)| := abs_add_le _ _
    _ = |a - b| * Real.log a + b * |Real.log a - Real.log b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hla0, abs_of_nonneg (by linarith : 0 ≤ b)]
    _ ≤ (4 * |x - y|) * 6 + 7 * ((4 * |x - y|) / 3) := by
        gcongr
        exact hlog.trans (by linarith)
    _ ≤ 34 * |x - y| := by nlinarith [abs_nonneg (x - y)]

theorem bound_g₂ : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g₂ x| ≤ 42 := fun x hx => by
  have ha : 3 ≤ 3 + x ^ 2 := by nlinarith
  have ha7 : 3 + x ^ 2 ≤ 7 := by nlinarith [hx.1, hx.2]
  have hl := log_le_six (by linarith) ha7
  have hl0 : 0 ≤ Real.log (3 + x ^ 2) := Real.log_nonneg (by linarith)
  rw [g₂, abs_of_nonneg (by positivity)]
  nlinarith

end Cubic.Counting.GeneralMonicIntegrals
