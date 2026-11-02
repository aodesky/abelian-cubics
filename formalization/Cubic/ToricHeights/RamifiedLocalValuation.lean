import Cubic.ToricHeights.RamifiedLocalHeight

/-!
# Integral valuation at three and its ramification factor

The square of the extension norm is a p-adic norm: for `x=a+bζ`, use
`x*conj(x)=a²+b²-ab`. Consequently `2 * logarithmicOrder x` is an integer
for every nonzero local element, not just the chosen parameter. The resulting
surjective valuation sends `ζ-1` to one and restricts to twice the base-field
valuation. This checks `ell_w/e₃` with `e₃=2` on the entire local group.
-/

noncomputable section

namespace Cubic.ToricHeights.RamifiedLocalModel

open Cubic.QuadraticCorrespondence.CyclotomicRamifiedField

private theorem norm_sq_exists (x : Points) :
    ∃ n : ℤ, ‖(x : Extension)‖ ^ 2 = (3 : ℝ) ^ (-n) := by
  obtain ⟨a, b, hx⟩ := exists_linear (x : Extension)
  have hmul : linear a b * conjugation (linear a b) =
      algebraMap ℚ_[3] Extension (a ^ 2 + b ^ 2 - a * b) := by
    rw [conjugation_linear]
    simp only [linear, map_add, map_sub, map_pow, map_mul]
    linear_combination -(algebraMap ℚ_[3] Extension b) ^ 2 * zeta_relation
  have hn : ‖(x : Extension)‖ ^ 2 = ‖a ^ 2 + b ^ 2 - a * b‖ := by
    have h := congrArg norm hmul
    simpa only [norm_mul, norm_conjugation,
      Cubic.QuadraticCorrespondence.CyclotomicRamifiedField.norm_algebraMap, ← pow_two, ← hx] using h
  have hn0 : a ^ 2 + b ^ 2 - a * b ≠ 0 := by
    intro h
    have hpos : 0 < ‖(x : Extension)‖ ^ 2 := pow_pos (norm_pos_iff.mpr x.ne_zero) _
    rw [hn, h, norm_zero] at hpos
    exact lt_irrefl _ hpos
  exact ⟨Padic.valuation (a ^ 2 + b ^ 2 - a * b),
    hn.trans (Padic.norm_eq_zpow_neg_valuation hn0)⟩

/-- The valuation normalized to give the cyclotomic parameter value one. -/
def ord (x : Points) : ℤ := Classical.choose (norm_sq_exists x)

theorem norm_sq_eq_zpow_ord (x : Points) :
    ‖(x : Extension)‖ ^ 2 = (3 : ℝ) ^ (-ord x) := Classical.choose_spec (norm_sq_exists x)

/-- The analytic coordinate defined from the base-field norm is `ord_w/e₃`. -/
theorem logarithmicOrder_eq_ord_div_two (x : Points) :
    logarithmicOrder x = (ord x : ℝ) / 2 := by
  have h := congrArg Real.log (norm_sq_eq_zpow_ord x)
  rw [Real.log_pow, Real.log_zpow] at h
  push_cast at h
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  unfold logarithmicOrder
  apply (div_eq_iff hlog).mpr
  linarith

theorem degree_eq_ord (x : Points) : degree x = (ord x : ℝ) := by
  rw [degree, logarithmicOrder_eq_ord_div_two]
  ring

@[simp]
theorem ord_one : ord 1 = 0 := by
  have h := logarithmicOrder_eq_ord_div_two 1
  rw [logarithmicOrder_one] at h
  exact_mod_cast (show (ord 1 : ℝ) = 0 by linarith)

theorem ord_mul (x y : Points) : ord (x * y) = ord x + ord y := by
  have h := logarithmicOrder_mul x y
  simp only [logarithmicOrder_eq_ord_div_two] at h
  exact_mod_cast (show (ord (x * y) : ℝ) = (ord x : ℝ) + (ord y : ℝ) by linarith)

def integerValuation : Points →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord x)
  map_one' := congrArg Multiplicative.ofAdd ord_one
  map_mul' x y := congrArg Multiplicative.ofAdd (ord_mul x y)

@[simp]
theorem ord_ramifiedParameter : ord ramifiedParameter = 1 := by
  have h := logarithmicOrder_eq_ord_div_two ramifiedParameter
  rw [logarithmicOrder_ramifiedParameter] at h
  exact_mod_cast (show (ord ramifiedParameter : ℝ) = 1 by linarith)

/-- All integral valuation values occur, including negative values. -/
theorem integerValuation_surjective : Function.Surjective integerValuation := by
  intro n
  refine ⟨ramifiedParameter ^ n.toAdd, ?_⟩
  rw [map_zpow]
  change Multiplicative.ofAdd (ord ramifiedParameter) ^ n.toAdd = n
  rw [ord_ramifiedParameter, ← ofAdd_zsmul]
  simp

/-- On every scalar, the integral extension valuation is twice the base valuation. -/
theorem ord_scalarUnits (x : ℚ_[3]ˣ) :
    ord (Units.map (algebraMap ℚ_[3] Extension).toMonoidHom x) =
      2 * Padic.valuation (x : ℚ_[3]) := by
  have h := logarithmicOrder_eq_ord_div_two
    (Units.map (algebraMap ℚ_[3] Extension).toMonoidHom x)
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  change -Real.log ‖algebraMap ℚ_[3] Extension (x : ℚ_[3])‖ / Real.log 3 = _ at h
  rw [Cubic.QuadraticCorrespondence.CyclotomicRamifiedField.norm_algebraMap,
    Padic.norm_eq_zpow_neg_valuation x.ne_zero, Real.log_zpow] at h
  push_cast at h
  have hs : (Padic.valuation (x : ℚ_[3]) : ℝ) =
      (ord (Units.map (algebraMap ℚ_[3] Extension).toMonoidHom x) : ℝ) / 2 := by
    simpa [neg_mul, hlog] using h
  exact_mod_cast (show (ord (Units.map (algebraMap ℚ_[3] Extension).toMonoidHom x) : ℝ) =
    2 * (Padic.valuation (x : ℚ_[3]) : ℝ) by linarith)

theorem ker_integerValuation : integerValuation.ker = compactUnits := by
  ext x
  change ord x = 0 ↔ x ∈ compactUnits
  rw [← logarithmicOrder_eq_zero_iff, logarithmicOrder_eq_ord_div_two]
  simp

end Cubic.ToricHeights.RamifiedLocalModel
