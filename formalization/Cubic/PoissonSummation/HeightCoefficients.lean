import CubicTargets.PoissonSummation.HeightCoefficients
import Cubic.PoissonSummation.HeightCountingIdentification

/-! The arithmetic formulas for the actual height coefficients, obtained by
Euler-factor comparison and multiplicativity. -/

namespace Cubic.PoissonSummation.HeightCoefficients
open HeightCountingData HeightCountingCoefficients

theorem inert {p : ℕ} (hp : p.Prime) (hr : p % 3 = 2) (k : ℕ) :
    coefficient (p ^ k) = if Even k then 1 else 0 := by
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    simpa only [two_mul] using inert_even hp hr j
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hk
    rw [hj]
    exact inert_odd hp hr j

theorem product {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    coefficient n = if ∀ p ∈ n.primeFactors, p % 3 = 2 → Even (n.factorization p)
      then ∏ p ∈ n.primeFactors.filter (fun p => p % 3 = 1),
        (3 * (n.factorization p : ℤ) + 1) else 0 := by
  classical
  rw [multiplicative.multiplicative_factorization _ hn.ne']
  simp only [Finsupp.prod, Nat.support_factorization]
  have hp3 : ∀ p ∈ n.primeFactors, p ≠ 3 := by
    intro p hp he
    exact h3 (he ▸ Nat.dvd_of_mem_primeFactors hp)
  have hres : ∀ p ∈ n.primeFactors, p % 3 = 1 ∨ p % 3 = 2 := by
    intro p hp
    have hnd : ¬ 3 ∣ p := fun h => hp3 p hp ((Nat.prime_of_mem_primeFactors hp).dvd_iff_eq
      (by decide) |>.mp h)
    omega
  split_ifs with hall
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    rcases hres p hp with hr | hr
    · simp only [hr, if_true]
      exact split (Nat.prime_of_mem_primeFactors hp) hr _
    · rw [inert (Nat.prime_of_mem_primeFactors hp) hr, if_pos (hall p hp hr)]
      simp [hr]
  · push_neg at hall
    obtain ⟨p, hp, hr, hk⟩ := hall
    exact Finset.prod_eq_zero hp (by rw [inert (Nat.prime_of_mem_primeFactors hp) hr, if_neg hk])

theorem «rem:heightCoefficients»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.HeightCoefficients.Claim := by
  refine ⟨HeightCountingSeries.count_eq_zero_of_three_dvd,
    HeightCountingIdentification.point_count hPoisson, fun n hn h3 => ?_⟩
  rw [HeightCountingIdentification.counts_eq_coefficient hPoisson]
  exact product hn h3

end Cubic.PoissonSummation.HeightCoefficients
