import Cubic.ToricHeights.InertLocalHeight
import Cubic.ToricHeights.LocalCoefficientIntegrality

/-!
# The coefficient-integrality cutoff at inert primes

For arbitrary cyclotomic coordinates over the base p-adic field, integrality
of the paper's two cubic coefficient expressions is equivalent to integrality
in the quadratic local field. This identifies the coefficient cutoff
with the norm-defined cutoff and hence the invariant lattice cone. The
comparison with the original local quotient is in `QuotientLocalIntegrality`.
-/

noncomputable section

namespace Cubic.ToricHeights.InertLocalIntegrality

open Cubic.QuadraticCorrespondence
open CyclotomicInertField
open CyclotomicCoefficients

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

omit [Fact p.Prime] in
private theorem prime_ne_three : p ≠ 3 := by
  have := (Fact.out : p % 3 = 2)
  omega

theorem linear_mul_conjugation (u v : ℚ_[p]) :
    linear p u v * conjugation p (linear p u v) =
      algebraMap ℚ_[p] (Extension p) (normForm u v) := by
  rw [conjugation_linear]
  simp only [linear, normForm, map_sub, map_add, map_pow, map_mul]
  linear_combination -(algebraMap ℚ_[p] (Extension p) v) ^ 2 * zeta_relation p

theorem norm_normForm (u v : ℚ_[p]) : ‖normForm u v‖ = ‖linear p u v‖ ^ 2 := by
  rw [← CyclotomicInertField.norm_algebraMap p (normForm u v),
    ← linear_mul_conjugation, norm_mul, norm_conjugation, pow_two]

/-- No coordinate-integrality hypothesis is needed: it follows from the norm bound. -/
theorem coefficientsIntegral_iff_norm (u v : ℚ_[p]) :
    LocalCoefficientIntegrality.CoefficientsIntegral p (normForm u v) (traceForm u v) ↔
      ‖linear p u v‖ ≤ 1 := by
  rw [LocalCoefficientIntegrality.coefficientsIntegral_iff p (prime_ne_three p), norm_normForm]
  constructor
  · rintro ⟨hN, _⟩
    nlinarith [norm_nonneg (linear p u v)]
  · intro h
    have hN : ‖normForm u v‖ ≤ 1 := by
      rw [norm_normForm]
      exact pow_le_one₀ (norm_nonneg _) h
    have huv : ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 := by
      rw [norm_linear] at h
      exact max_le_iff.mp h
    have hT : ‖traceForm u v‖ ≤ 1 := by
      change traceForm u v ∈ PadicInt.subring p
      exact (PadicInt.subring p).sub_mem
        ((PadicInt.subring p).mul_mem (natCast_mem (PadicInt.subring p) 2) huv.1) huv.2
    exact ⟨by rwa [norm_normForm] at hN, by rw [norm_mul]; exact mul_le_one₀ hN (norm_nonneg _) hT⟩

/-- The cutoff defined by the explicit cubic coefficients, on field units. -/
def coefficientLocus : Set (InertLocalModel.Points p) :=
  {x | ∃ u v : ℚ_[p], (x : Extension p) = linear p u v ∧
    LocalCoefficientIntegrality.CoefficientsIntegral p (normForm u v) (traceForm u v)}

theorem coefficientLocus_eq_integralLocus : coefficientLocus p = InertLocalModel.integralLocus p := by
  ext x
  constructor
  · rintro ⟨u, v, hx, hc⟩
    change ‖(x : Extension p)‖ ≤ 1
    rw [hx]
    exact (coefficientsIntegral_iff_norm p u v).mp hc
  · intro hx
    obtain ⟨u, v, huv⟩ := exists_linear p (x : Extension p)
    refine ⟨u, v, huv, (coefficientsIntegral_iff_norm p u v).mpr ?_⟩
    exact huv ▸ hx

end Cubic.ToricHeights.InertLocalIntegrality
