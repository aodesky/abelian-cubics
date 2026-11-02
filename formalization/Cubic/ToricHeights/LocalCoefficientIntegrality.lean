import Cubic.QuadraticCorrespondence.CyclotomicCoefficients
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Cubic coefficient integrality away from three

For the monic trace-one cubic attached to norm `N` and trace `T`, the variable
coefficients are `(1-N)/3` and `(N(3-T)-1)/27`. Away from three their integrality
is equivalent to integrality of `N` and `NT`. This is shared by the split and
inert local calculations; it does not assume their geometric interpretation.
-/

noncomputable section

namespace Cubic.ToricHeights.LocalCoefficientIntegrality

variable (p : ℕ) [Fact p.Prime]

/-- A root of a monic quadratic with integral coefficients is p-adically integral. -/
theorem norm_le_one_of_quadratic {a b z : ℚ_[p]}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hz : z ^ 2 = a * z - b) : ‖z‖ ≤ 1 := by
  by_contra h
  have hz1 : 1 < ‖z‖ := lt_of_not_ge h
  have hmul : ‖a * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) ha
  have hsq : ‖z‖ ^ 2 ≤ max ‖a * z‖ ‖b‖ := by
    rw [← norm_pow, hz]
    simpa only [sub_eq_add_neg, norm_neg] using Padic.nonarchimedean (a * z) (-b)
  have := hsq.trans (max_le hmul (hb.trans hz1.le))
  nlinarith

/-- Integrality of the paper's explicit cubic coefficient expressions. -/
def CoefficientsIntegral (N T : ℚ_[p]) : Prop :=
  ‖(1 - N) / 3‖ ≤ 1 ∧ ‖(N * (3 - T) - 1) / 27‖ ≤ 1

theorem norm_three (hp : p ≠ 3) : ‖(3 : ℚ_[p])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro h
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hp h

theorem norm_twentySeven (hp : p ≠ 3) : ‖(27 : ℚ_[p])‖ = 1 := by
  have h : (27 : ℚ_[p]) = 3 ^ 3 := by norm_num
  rw [h, norm_pow, norm_three p hp, one_pow]

theorem norm_sub_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  have h : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
    simpa only [sub_eq_add_neg, norm_neg] using Padic.nonarchimedean a (-b)
  exact h.trans (max_le ha hb)

theorem norm_sub_le_one_iff {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    ‖a - b‖ ≤ 1 ↔ ‖b‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => norm_sub_le_one p ha h⟩
  simpa only [sub_sub_cancel] using norm_sub_le_one p ha h

theorem norm_sub_one_le_one_iff (a : ℚ_[p]) : ‖a - 1‖ ≤ 1 ↔ ‖a‖ ≤ 1 := by
  rw [norm_sub_rev]
  exact norm_sub_le_one_iff p (by simp)

/-- Clearing the unit denominators gives exactly the two norm/trace bounds. -/
theorem coefficientsIntegral_iff (hp : p ≠ 3) (N T : ℚ_[p]) :
    CoefficientsIntegral p N T ↔ ‖N‖ ≤ 1 ∧ ‖N * T‖ ≤ 1 := by
  unfold CoefficientsIntegral
  rw [norm_div, norm_three p hp, div_one, norm_div, norm_twentySeven p hp, div_one,
    norm_sub_le_one_iff p (by simp), norm_sub_one_le_one_iff]
  apply and_congr_right
  intro hN
  rw [mul_sub]
  exact norm_sub_le_one_iff p (by simpa [norm_mul, norm_three p hp] using hN)

end Cubic.ToricHeights.LocalCoefficientIntegrality
