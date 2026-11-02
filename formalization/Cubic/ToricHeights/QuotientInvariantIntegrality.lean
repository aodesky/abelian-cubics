import Cubic.ToricHeights.DescendedCyclicInvariant
import Cubic.ToricHeights.QuotientLocalIntegrality

/-!
# Integrality of all three original local invariants

The paper defines its finite cutoff using `e₂`, `e₃` and `δ`. The quadratic
relation for the original descended `δ` shows that the third condition follows
from the first two, over every p-adic field. This includes the exceptional
prime, where the coefficient comparison of `QuotientLocalIntegrality` gives `1+3O`.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientInvariantIntegrality

open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients
open DescendedCyclicInvariant

variable (p : ℕ) [Fact p.Prime]

/-- All three regular functions in the paper's finite cutoff.
The cubic constant coefficient is `-e₃`, so the second condition uses its negative. -/
def invariantLocus : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  {P | ‖P linearCoefficient‖ ≤ 1 ∧ ‖-P constantCoefficient‖ ≤ 1 ∧ ‖P delta‖ ≤ 1}

/-- Integrality of the cyclic invariant follows from its original monic quadratic. -/
theorem delta_integral (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (ha : ‖P linearCoefficient‖ ≤ 1) (hb : ‖P constantCoefficient‖ ≤ 1) : ‖P delta‖ ≤ 1 := by
  apply LocalCoefficientIntegrality.norm_le_one_of_quadratic p (z := P delta)
    (a := P linearCoefficient + 3 * P constantCoefficient)
    (b := P linearCoefficient ^ 3 - P constantCoefficient + 9 * P constantCoefficient ^ 2 +
      6 * P linearCoefficient * P constantCoefficient)
  · change P linearCoefficient + 3 * P constantCoefficient ∈ PadicInt.subring p
    exact (PadicInt.subring p).add_mem ha
      ((PadicInt.subring p).mul_mem (natCast_mem (PadicInt.subring p) 3) hb)
  · change P linearCoefficient ^ 3 - P constantCoefficient + 9 * P constantCoefficient ^ 2 +
      6 * P linearCoefficient * P constantCoefficient ∈ PadicInt.subring p
    exact (PadicInt.subring p).add_mem
      ((PadicInt.subring p).add_mem
        ((PadicInt.subring p).sub_mem ((PadicInt.subring p).pow_mem ha 3) hb)
        ((PadicInt.subring p).mul_mem (natCast_mem (PadicInt.subring p) 9)
          ((PadicInt.subring p).pow_mem hb 2)))
      ((PadicInt.subring p).mul_mem
        ((PadicInt.subring p).mul_mem (natCast_mem (PadicInt.subring p) 6) ha) hb)
  · exact delta_quadratic_at P

/-- The full three-function cutoff equals integrality of the original cubic coefficients. -/
theorem invariantLocus_eq_coefficientLocus :
    invariantLocus p = QuotientLocalIntegrality.coefficientLocus p := by
  ext P
  change (‖P linearCoefficient‖ ≤ 1 ∧ ‖-P constantCoefficient‖ ≤ 1 ∧ ‖P delta‖ ≤ 1) ↔
    (‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1)
  rw [norm_neg]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, delta_integral p P h.1 h.2⟩⟩

/-- The paper's three original invariants give exactly the split Fourier cutoff. -/
theorem split_mem_iff [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ invariantLocus p ↔
      SplitQuotientLogarithm.localPoint p P ∈ SplitLocalIntegrality.coefficientLocus p := by
  rw [invariantLocus_eq_coefficientLocus, QuotientLocalIntegrality.split_mem_iff]

/-- The full cutoff at an inert prime, including two. -/
theorem inert_mem_iff [Fact (p % 3 = 2)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ invariantLocus p ↔
      InertQuotientLogarithm.localPoint p P ∈ InertLocalIntegrality.coefficientLocus p := by
  rw [invariantLocus_eq_coefficientLocus, QuotientLocalIntegrality.inert_mem_iff]

/-- The full cutoff at three is the subgroup used for the factor `1/6`. -/
theorem ramified_mem_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    P ∈ invariantLocus 3 ↔
      RamifiedQuotientLogarithm.localPoint P ∈ RamifiedLocalIntegrality.coefficientLocus := by
  rw [invariantLocus_eq_coefficientLocus, QuotientLocalIntegrality.ramified_mem_iff]

end Cubic.ToricHeights.QuotientInvariantIntegrality
