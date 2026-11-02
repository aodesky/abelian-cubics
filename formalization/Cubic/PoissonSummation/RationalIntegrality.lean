import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Integer rationals from all finite-place bounds

The denominator criterion needed to identify globally integral cyclotomic
coefficients from the local compact conditions. Every rational prime is used.
-/

namespace Cubic.PoissonSummation.RationalIntegrality

theorem denominator_not_dvd (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ‖(q : ℚ_[p])‖ ≤ 1) : ¬p ∣ q.den := by
  intro hd
  have hn : ¬(p : ℤ) ∣ q.num := by
    intro hn
    exact Nat.not_coprime_of_dvd_of_dvd (Fact.out : p.Prime).one_lt
      (Int.natCast_dvd.mp hn) hd q.reduced
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 := by
    apply Padic.norm_intCast_eq_one_iff.mpr
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast,
      ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm,
      (Fact.out : p.Prime).coprime_iff_not_dvd]
    exact fun h => hn (Int.natCast_dvd.mpr h)
  have hdlt : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have hdpos : 0 < ‖(q.den : ℚ_[p])‖ := norm_pos_iff.mpr (by exact_mod_cast q.den_ne_zero)
  have he : (q : ℚ_[p]) = (q.num : ℚ_[p]) / (q.den : ℚ_[p]) := by
    exact_mod_cast q.num_div_den.symm
  rw [he, norm_div, hn1, div_le_one hdpos] at hq
  exact (not_lt_of_ge hq) hdlt

theorem exists_int_of_forall_norm_le_one (q : ℚ)
    (hq : ∀ p : ℕ, ∀ _ : Fact p.Prime, ‖(q : ℚ_[p])‖ ≤ 1) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have hd : q.den = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr (fun p hp => by
    letI : Fact p.Prime := ⟨hp⟩
    exact denominator_not_dvd p q (hq p inferInstance))
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one hd⟩

end Cubic.PoissonSummation.RationalIntegrality
