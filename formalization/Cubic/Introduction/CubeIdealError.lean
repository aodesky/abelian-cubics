import Cubic.Introduction.CubeIdealSumData
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Elementary changes of scale for the error in Kühleitner--Nowak. -/

noncomputable section

namespace Cubic.Introduction.CubeIdealError

open Filter Asymptotics CubeIdealSumData

theorem log_lower {X : ℝ} (hX : Real.exp 1 ≤ X) : 1 ≤ Real.log X := by
  simpa using Real.log_le_log (Real.exp_pos 1) hX

theorem error_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ error X := by
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (pow_nonneg (Real.log_nonneg hX) _)) (sq_nonneg _)

theorem error_mono {X Y : ℝ} (hX : Real.exp 1 ≤ X) (hXY : X ≤ Y) :
    error X ≤ error Y := by
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlX := log_lower hX
  have hlY := log_lower (hX.trans hXY)
  have hl := Real.log_le_log hX0 hXY
  have hll := Real.log_le_log (by linarith : 0 < Real.log X) hl
  dsimp [error]
  gcongr
  exact Real.log_nonneg hlX

theorem divide_three :
    (fun X : ℝ => error (X / 3)) =O[atTop] error := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (3 * Real.exp 1)] with X hX
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hsmall : Real.exp 1 ≤ X / 3 := by linarith
  have hX1 : 1 ≤ X := by linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (error_nonneg hX1),
    abs_of_nonneg (error_nonneg (he.trans hsmall)), one_mul] using
      error_mono hsmall (by linarith : X / 3 ≤ X)

theorem height_bound (H X : ℝ) (hH : 1 ≤ H)
    (hl : 2 ≤ Real.log H) (hll : 3 ≤ Real.log (Real.log H))
    (hX : Real.exp 1 ≤ X) (hupper : X ≤ 4 * H ^ 2) :
    error X ≤ 512 * heightError H := by
  have hH0 : 0 < H := by linarith
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlX := log_lower hX
  have hfour : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hsqrt : Real.sqrt X ≤ 2 * H := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * H)).mpr
    nlinarith
  have hlog : Real.log X ≤ 4 * Real.log H := by
    have h := Real.log_le_log hX0 hupper
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hH0.ne'), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hloglog : Real.log (Real.log X) ≤ 2 * Real.log (Real.log H) := by
    have h := Real.log_le_log (by linarith : 0 < Real.log X) hlog
    rw [Real.log_mul (by norm_num) (by linarith : Real.log H ≠ 0)] at h
    linarith
  calc
    error X ≤ (2 * H) * (4 * Real.log H) ^ 3 * (2 * Real.log (Real.log H)) ^ 2 := by
      dsimp [error]
      gcongr
      exact Real.log_nonneg hlX
    _ = 512 * heightError H := by dsimp [heightError]; ring

theorem height_comp (f : ℝ → ℝ)
    (hf : ∀ᶠ H : ℝ in atTop, Real.exp 1 ≤ f H ∧ f H ≤ 4 * H ^ 2) :
    (fun H => error (f H)) =O[atTop] heightError := by
  apply IsBigO.of_bound 512
  filter_upwards [hf, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (3 : ℝ))] with H hf hH hl hll
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hh : 0 ≤ heightError H := by
    dsimp [heightError]
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (error_nonneg (he.trans hf.1)),
    abs_of_nonneg hh] using height_bound H (f H) hH hl hll hf.1 hf.2

theorem square :
    (fun H : ℝ => error (H ^ 2)) =O[atTop] heightError := by
  apply height_comp
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 : ℝ)]
    with H he hH
  exact ⟨he.trans (by nlinarith), by nlinarith [sq_nonneg H]⟩

theorem shifted_square :
    (fun H : ℝ => error (3 * H ^ 2 + 1)) =O[atTop] heightError := by
  apply height_comp
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 : ℝ)]
    with H he hH
  exact ⟨he.trans (by nlinarith), by nlinarith⟩

theorem identity_height :
    (fun H : ℝ => H) =O[atTop] heightError := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with H hH hl hll
  have h1 := one_le_pow₀ hl (n := 3)
  have h2 := one_le_pow₀ hll (n := 2)
  have hh : H ≤ heightError H := by
    exact (le_mul_of_one_le_right (by linarith : 0 ≤ H) h1).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ H * Real.log H ^ 3) h2)
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ H),
    abs_of_nonneg (by linarith : 0 ≤ heightError H)] using hh

theorem sqrt_error :
    (fun X : ℝ => Real.sqrt X) =O[atTop] error := by
  apply IsBigO.of_bound 1
  filter_upwards [
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with X hl hll
  have h1 := one_le_pow₀ hl (n := 3)
  have h2 := one_le_pow₀ hll (n := 2)
  have hh : Real.sqrt X ≤ error X :=
    (le_mul_of_one_le_right (Real.sqrt_nonneg X) h1).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ Real.sqrt X * Real.log X ^ 3) h2)
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg X),
    abs_of_nonneg ((Real.sqrt_nonneg X).trans hh)] using hh

end Cubic.Introduction.CubeIdealError
