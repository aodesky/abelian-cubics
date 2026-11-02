import Cubic.QuadraticCorrespondence.QuotientCoefficientFormula
import Cubic.ToricHeights.SplitQuotientLogarithm
import Cubic.ToricHeights.InertQuotientLogarithm
import Cubic.ToricHeights.RamifiedQuotientLogarithm
import Cubic.ToricHeights.SplitLocalIntegrality
import Cubic.ToricHeights.InertLocalIntegrality
import Cubic.ToricHeights.RamifiedLocalIntegrality

/-!
# Original quotient coefficients and the finite Fourier cutoffs

Define integrality using the original descended symmetric coefficient functions.
On every local quotient point it agrees with the coefficient cutoffs used in
the split, inert and ramified Fourier integrals. In particular, at three this
is precisely `1+3O`, not merely the first principal congruence level.

No cover lift or coordinate-integrality hypothesis is imposed. Integrality of
the third invariant `δ` follows from that of the coefficients
(`QuotientInvariantIntegrality`).
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientLocalIntegrality

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois CyclotomicRestrictionScalars
open DescendedCoefficients (linearCoefficient constantCoefficient)
open CyclotomicCoefficients (normForm traceForm)

/-- Integrality of the original descended cubic coefficients, before any coordinate formula. -/
def coefficientLocus (p : ℕ) [Fact p.Prime] : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  {P | ‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1}

section Split

open SplitQuotientLogarithm

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]

/-- The original local cubic has the split norm/trace coefficients on every quotient point. -/
theorem split_coefficients (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    let x := localPoint p P
    P linearCoefficient = (1 - (x.1 : ℚ_[p]) * (x.2 : ℚ_[p])) / 3 ∧
      P constantCoefficient =
        ((x.1 : ℚ_[p]) * (x.2 : ℚ_[p]) * (3 - ((x.1 : ℚ_[p]) + (x.2 : ℚ_[p]))) - 1) / 27 := by
  have hc := congrArg Units.val (mapped_conjugate p (quotientRestrictionScalarsEquiv ℚ_[p] P))
  change place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) =
    ((localPoint p P).2 : ℚ_[p]) at hc
  apply QuotientCoefficientFormula.coefficients_eq_of_norm_trace (RingHom.id ℚ_[p]) (place p)
  · intro a
    exact congrArg Prod.fst (splitting_scalar p a)
  · change place p (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) *
      place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) = _
    rw [hc]
    rfl
  · change place p (quotientRestrictionScalarsEquiv ℚ_[p] P : E ⊗[ℚ] ℚ_[p]) +
      place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) = _
    rw [hc]
    rfl

theorem split_mem_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ coefficientLocus p ↔ localPoint p P ∈ SplitLocalIntegrality.coefficientLocus p := by
  change (‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1) ↔ _
  rw [(split_coefficients p P).1, (split_coefficients p P).2]
  rfl

/-- The original coefficient cutoff is the cone in the character-defined enlarged lattice. -/
theorem split_mem_iff_cone (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ coefficientLocus p ↔ Cubic.PoissonSummation.LatticeCone.InCone
      (QuotientLocalCharacters.localCocharacter ℚ_[p] (place p)
        (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) P) := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  rw [split_mem_iff, SplitLocalIntegrality.coefficientLocus_eq_integralLocus p hp,
    localCocharacter_eq]
  rfl

end Split

section Inert

open InertQuotientLogarithm
open CyclotomicInertField (Extension linear conjugation)

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

/-- The original coefficients in arbitrary inert cyclotomic coordinates.
The coordinates need not be integral; the norm bound will follow from coefficient integrality. -/
theorem inert_coefficients (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (a b : ℚ_[p])
    (hx : (localPoint p P : Extension p) = linear p a b) :
    P linearCoefficient = CyclotomicCoefficients.linearCoefficient a b ∧
      P constantCoefficient = CyclotomicCoefficients.constantCoefficient a b := by
  have hc := congrArg Units.val (mapped_conjugate p (quotientRestrictionScalarsEquiv ℚ_[p] P))
  change place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) =
    conjugation p (localPoint p P : Extension p) at hc
  apply QuotientCoefficientFormula.coefficients_eq_of_norm_trace
    (algebraMap ℚ_[p] (Extension p)) (place p).toRingHom (place_scalar p)
  · change (localPoint p P : Extension p) *
      place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) = _
    rw [hc]
    rw [hx, InertLocalIntegrality.linear_mul_conjugation]
  · change (localPoint p P : Extension p) +
      place p (conjugateUnit ℚ_[p] (quotientRestrictionScalarsEquiv ℚ_[p] P) : E ⊗[ℚ] ℚ_[p]) = _
    rw [hc]
    rw [hx, CyclotomicInertField.conjugation_linear]
    simp only [linear, traceForm, map_sub, map_mul, map_ofNat]
    ring

theorem inert_mem_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ coefficientLocus p ↔ localPoint p P ∈ InertLocalIntegrality.coefficientLocus p := by
  constructor
  · intro h
    obtain ⟨a, b, hx⟩ := CyclotomicInertField.exists_linear p (localPoint p P : Extension p)
    refine ⟨a, b, hx, ?_⟩
    change ‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1 at h
    rw [(inert_coefficients p P a b hx).1, (inert_coefficients p P a b hx).2] at h
    exact h
  · rintro ⟨a, b, hx, h⟩
    change ‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1
    rw [(inert_coefficients p P a b hx).1, (inert_coefficients p P a b hx).2]
    exact h

/-- The original coefficient integrality forces the local field parameter to be integral. -/
theorem inert_mem_iff_norm (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    P ∈ coefficientLocus p ↔ ‖(localPoint p P : Extension p)‖ ≤ 1 := by
  rw [inert_mem_iff, InertLocalIntegrality.coefficientLocus_eq_integralLocus]
  rfl

end Inert

section Ramified

open RamifiedQuotientLogarithm
open CyclotomicRamifiedField (Extension linear conjugation integers)

/-- The same original coefficients at three, retaining both nonunit denominators. -/
theorem ramified_coefficients (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) (a b : ℚ_[3])
    (hx : (localPoint P : Extension) = linear a b) :
    P linearCoefficient = CyclotomicCoefficients.linearCoefficient a b ∧
      P constantCoefficient = CyclotomicCoefficients.constantCoefficient a b := by
  have hc := congrArg Units.val (mapped_conjugate (quotientRestrictionScalarsEquiv ℚ_[3] P))
  change place (conjugateUnit ℚ_[3] (quotientRestrictionScalarsEquiv ℚ_[3] P) : E ⊗[ℚ] ℚ_[3]) =
    conjugation (localPoint P : Extension) at hc
  apply QuotientCoefficientFormula.coefficients_eq_of_norm_trace
    (algebraMap ℚ_[3] Extension) place.toRingHom place_scalar
  · change (localPoint P : Extension) *
      place (conjugateUnit ℚ_[3] (quotientRestrictionScalarsEquiv ℚ_[3] P) : E ⊗[ℚ] ℚ_[3]) = _
    rw [hc]
    rw [hx, RamifiedLocalIntegrality.linear_mul_conjugation]
  · change (localPoint P : Extension) +
      place (conjugateUnit ℚ_[3] (quotientRestrictionScalarsEquiv ℚ_[3] P) : E ⊗[ℚ] ℚ_[3]) = _
    rw [hc]
    rw [hx, CyclotomicRamifiedField.conjugation_linear]
    simp only [linear, traceForm, map_sub, map_mul, map_ofNat]
    ring

theorem ramified_mem_iff (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    P ∈ coefficientLocus 3 ↔ localPoint P ∈ RamifiedLocalIntegrality.coefficientLocus := by
  constructor
  · intro h
    obtain ⟨a, b, hx⟩ := CyclotomicRamifiedField.exists_linear (localPoint P : Extension)
    refine ⟨a, b, hx, ?_⟩
    change ‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1 at h
    rw [(ramified_coefficients P a b hx).1, (ramified_coefficients P a b hx).2] at h
    exact h
  · rintro ⟨a, b, hx, h⟩
    change ‖P linearCoefficient‖ ≤ 1 ∧ ‖P constantCoefficient‖ ≤ 1
    rw [(ramified_coefficients P a b hx).1, (ramified_coefficients P a b hx).2]
    exact h

/-- For the original descended coefficients the exceptional cutoff is precisely `1+3O`. -/
theorem ramified_mem_iff_congruence (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    P ∈ coefficientLocus 3 ↔ ∃ a : integers, (localPoint P : Extension) = 1 + 3 * (a : Extension) := by
  rw [ramified_mem_iff, RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus,
    RamifiedLocalModel.mem_integralLocus_iff_exists]

end Ramified

end Cubic.ToricHeights.QuotientLocalIntegrality
