import CubicTargets.BoxAsymptotic.AdditiveLargeSieve
import Cubic.BoxAsymptotic.AngularSpacing
import Cubic.BoxAsymptotic.AngularSeriesData

/-! Applying the cited additive large sieve to primitive Eisenstein vectors.
This proves the spacing specialization used in `lem:angularLargeSieve`. Grouping
ideals by primitive rays and controlling the variable cutoff remain separate
obligations; neither is included in the literature hypothesis. -/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimitiveLargeSieve

open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularSpacing
open Cubic.BoxAsymptotic.EisensteinCoordinates
open scoped BigOperators

theorem separated {R : ℕ} (v : Fin R → ℤ × ℤ) (hv : Function.Injective v)
    (hp : ∀ r, prim (v r)) {Y : ℝ} (hY : 0 < Y)
    (hN : ∀ r, (nrm (v r) : ℝ) ≤ Y) (r s : Fin R) (hrs : r ≠ s) (m : ℤ) :
    Real.sqrt 3 / (4 * Real.pi * Y) ≤
      |Complex.arg (eis (v r)) / (2 * Real.pi) -
        Complex.arg (eis (v s)) / (2 * Real.pi) - m| := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := spacing (hp r) (hp s) (fun h => hrs (hv h)) (hN r) (hN s) m 0
  have he : (Complex.arg (eis (v r)) - 2 * Real.pi * m) -
      (Complex.arg (eis (v s)) - 2 * Real.pi * (0 : ℤ)) =
      (2 * Real.pi) * (Complex.arg (eis (v r)) / (2 * Real.pi) -
        Complex.arg (eis (v s)) / (2 * Real.pi) - m) := by
    push_cast
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hπ] at h
  have hdiv : Real.sqrt 3 / (2 * Y) / (2 * Real.pi) ≤
      |Complex.arg (eis (v r)) / (2 * Real.pi) -
        Complex.arg (eis (v s)) / (2 * Real.pi) - m| :=
    (div_le_iff₀ hπ).mpr (by nlinarith only [h])
  convert hdiv using 1
  field_simp
  ring

/-- The additive large sieve specialized to any finite family of distinct
primitive Eisenstein vectors of norm at most `Y`. -/
theorem primitive_large_sieve
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    {R N : ℕ} (hN : 0 < N) (M : ℤ) (v : Fin R → ℤ × ℤ)
    (hv : Function.Injective v) (hp : ∀ r, prim (v r))
    {Y : ℝ} (hY : 0 < Y) (hNY : ∀ r, (nrm (v r) : ℝ) ≤ Y) (c : Fin R → ℂ) :
    (∑ n : Fin N, ‖∑ r : Fin R, c r * phase (M + (n : ℤ) + 1) (eis (v r))‖ ^ 2) ≤
      ((N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3) * ∑ r : Fin R, ‖c r‖ ^ 2 := by
  have h := hLS R N hN M (fun r => Complex.arg (eis (v r)) / (2 * Real.pi)) c
    (Real.sqrt 3 / (4 * Real.pi * Y)) (by positivity) (separated v hv hp hY hNY)
  have he (a θ : ℝ) : 2 * Real.pi * a * (θ / (2 * Real.pi)) = a * θ := by
    field_simp
  simp only [he, inv_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_one] at h
  simpa only [phase, character_eq_exp, Int.cast_add, Int.cast_natCast, Int.cast_one] using h

end Cubic.BoxAsymptotic.PrimitiveLargeSieve
