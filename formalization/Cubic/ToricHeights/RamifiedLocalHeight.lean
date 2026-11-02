import Cubic.ToricHeights.RamifiedLocalModel
import Cubic.ToricHeights.SupportFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Height and spectral character at three

Use the extension of the `ℚ₃` norm to define the real logarithmic coordinate
`r = -log ‖x‖ / log 3`. The support-function argument is `(r,r)`, which
incorporates the paper's factor `1/e₃`: the cyclotomic parameter `ζ-1` has
coordinate `r=1/2`, while the scalar three has coordinate one.

The full height and character are defined on all local units before applying
the `1+3𝓞` cutoff. Their restrictions to the maximal compact are one.
The comparison with the original local quotient is in `QuotientLocalModels`
and `RamifiedQuotientLogarithm`.
-/

noncomputable section

namespace Cubic.ToricHeights.RamifiedLocalModel

open Cubic.QuadraticCorrespondence.CyclotomicRamifiedField
  (Extension zeta zeta_relation norm_zeta norm_three mem_compactUnits_iff_norm_one)

/-- The valuation normalized on the rational base field, with real codomain. -/
def logarithmicOrder (x : Points) : ℝ := -Real.log ‖(x : Extension)‖ / Real.log 3

@[simp]
theorem logarithmicOrder_one : logarithmicOrder 1 = 0 := by simp [logarithmicOrder]

theorem logarithmicOrder_mul (x y : Points) :
    logarithmicOrder (x * y) = logarithmicOrder x + logarithmicOrder y := by
  simp only [logarithmicOrder, Units.val_mul, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr x.ne_zero) (norm_ne_zero_iff.mpr y.ne_zero)]
  ring

theorem continuous_logarithmicOrder : Continuous logarithmicOrder :=
  (((continuous_norm.comp Units.continuous_val).log
    (fun x => norm_ne_zero_iff.mpr x.ne_zero)).neg).div_const _

theorem logarithmicOrder_eq_zero_iff (x : Points) :
    logarithmicOrder x = 0 ↔ x ∈ compactUnits := by
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  rw [logarithmicOrder, div_eq_zero_iff, or_iff_left hlog, neg_eq_zero,
    mem_compactUnits_iff_norm_one]
  exact ⟨Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr x.ne_zero),
    fun h => by rw [h, Real.log_one]⟩

def scalarThree : Points := Units.mk0 3 (norm_ne_zero_iff.mp (by rw [norm_three]; norm_num))

theorem logarithmicOrder_scalarThree : logarithmicOrder scalarThree = 1 := by
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  simp [logarithmicOrder, scalarThree, norm_three, hlog]

theorem norm_zeta_sub_one_sq : ‖zeta - 1‖ ^ 2 = 1 / 3 := by
  have h : (zeta - 1) ^ 2 = -3 * zeta := by linear_combination zeta_relation
  rw [← norm_pow, h, norm_mul, norm_neg, norm_three, norm_zeta, mul_one]

/-- The ramified cyclotomic parameter, regarded as a unit of the field. -/
def ramifiedParameter : Points := Units.mk0 (zeta - 1) (by
  intro h
  have := norm_zeta_sub_one_sq
  norm_num [h] at this)

/-- This checks the ramification normalization used by the height. -/
theorem logarithmicOrder_ramifiedParameter : logarithmicOrder ramifiedParameter = 1 / 2 := by
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  have h : 2 * Real.log ‖zeta - 1‖ = -Real.log 3 := by
    have := congrArg Real.log norm_zeta_sub_one_sq
    simpa [Real.log_pow, Real.log_div] using this
  change -Real.log ‖zeta - 1‖ / Real.log 3 = 1 / 2
  apply (div_eq_iff hlog).mpr
  linarith

/-- Real cocharacter coordinates after dividing the integral valuation by `e₃`. -/
def rayCoordinates (x : Points) : ℝ × ℝ := (logarithmicOrder x, logarithmicOrder x)

def degree (x : Points) : ℝ := 2 * logarithmicOrder x

theorem degree_mul (x y : Points) : degree (x * y) = degree x + degree y := by
  simp only [degree, logarithmicOrder_mul, mul_add]

/-- The cubic support-function height on the whole local group. -/
def inverseHeight (s₀ σ : ℂ) (x : Points) : ℂ :=
  (3 : ℂ) ^ supportFunction s₀ σ (rayCoordinates x)

theorem inverseHeight_on_compactUnits (s₀ σ : ℂ) (x : Points) (hx : x ∈ compactUnits) :
    inverseHeight s₀ σ x = 1 := by
  have hr := (logarithmicOrder_eq_zero_iff x).mpr hx
  simp [inverseHeight, rayCoordinates, hr, supportFunction]

/-- The spectral character has the same inverse-Fourier sign as the other places. -/
def character (t : ℝ) : PontryaginDual Points where
  toFun x := Circle.exp (-Real.pi * t * Real.log 3 * degree x)
  map_one' := by simp [degree]
  map_mul' x y := by rw [degree_mul, mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_const.mul continuous_logarithmicOrder))

@[simp]
theorem character_zero : character 0 = 1 := by
  apply DFunLike.ext
  intro x
  change Circle.exp (-Real.pi * 0 * Real.log 3 * degree x) = 1
  simp

theorem character_on_compactUnits (t : ℝ) (x : Points) (hx : x ∈ compactUnits) :
    character t x = 1 := by
  have hr := (logarithmicOrder_eq_zero_iff x).mpr hx
  change Circle.exp (-Real.pi * t * Real.log 3 * degree x) = 1
  simp [degree, hr]

theorem character_eq_cpow (t : ℝ) (x : Points) :
    ((character t x : Circle) : ℂ) =
      (3 : ℂ) ^ (-Real.pi * Complex.I * (t : ℂ) * (degree x : ℂ)) := by
  change Complex.exp (((-Real.pi * t * Real.log 3 * degree x) : ℝ) * Complex.I) = _
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0)]
  have hlog : Complex.log (3 : ℂ) = (Real.log 3 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)).symm
  rw [hlog]
  push_cast
  congr 1
  ring

end Cubic.ToricHeights.RamifiedLocalModel
