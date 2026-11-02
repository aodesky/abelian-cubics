import Cubic.PoissonSummation.RationalLocalIntegers
import Cubic.PoissonSummation.RationalIntegrality
import Cubic.PoissonSummation.RationalUnitReduction

/-!
# Integer units are exactly the rational compact points

This supplies the local-to-global assertion in `lemma:KprimeGroup`. A rational
point in every finite maximal compact has integral coefficients in the global
cyclotomic basis. Applying the same fact to its inverse gives an actual unit
of the ring of integers, with the prescribed rational torus parametrization.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalCompactIntegers

open NumberField
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicField RationalParameterBaseChange RationalAdelicEmbedding
open AdelicCompactQuotient CyclotomicIntegerUnits RationalUnitReduction
open QuotientFiniteFourierProduct FiniteEulerProduct
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open scoped RationalQuotientGroup

private theorem transport_compact_membership {A : Type*} [Mul A]
    {D F : LocalData} (h : D = F) (e : F.Carrier ≃* A) (x : A) :
    ((congrArg (fun D => D.Carrier ≃* A) h).mpr e).symm x ∈ D.maxCompact ↔
      e.symm x ∈ F.maxCompact := by
  subst F
  rfl

theorem local_coefficients_of_compact (p : Nat.Primes) (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta)
    (hc : localPoint p P ∈ (family p).maxCompact) :
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖(b : ℚ_[p])‖ ≤ 1 := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  change (originalEquiv p).symm (baseChange ℚ_[p] P) ∈ (family p).maxCompact at hc
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    simp only [originalEquiv, dif_pos hs] at hc
    have h := (transport_compact_membership (family_split ⟨p, hs⟩) (MulEquiv.refl _)
      (baseChange ℚ_[p] P)).mp hc
    exact RationalLocalIntegers.split_coefficients_of_compact p P a b hP h
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    simp only [originalEquiv, dif_neg hs, dif_pos hi] at hc
    have h := (transport_compact_membership (family_inert ⟨p, hi⟩) (MulEquiv.refl _)
      (baseChange ℚ_[p] P)).mp hc
    exact RationalLocalIntegers.inert_coefficients_of_compact p P a b hP h
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    have hp : p = primeThree := Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst p
    exact RationalLocalIntegers.ramified_coefficients_of_compact P a b hP hc

/-- The rational parameter belongs to the genuine ring of integers. -/
theorem exists_integer_parameter (P : Points) (hc : finiteDiagonal P ∈ finiteCompact) :
    ∃ x : Integers, (x : E) = (parameterEquiv P : E) := by
  obtain ⟨a, b, hP⟩ := CyclotomicField.exists_linear (parameterEquiv P : E)
  have hlocal (p : ℕ) (hp : Fact p.Prime) :
      ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖(b : ℚ_[p])‖ ≤ 1 :=
    local_coefficients_of_compact ⟨p, hp.out⟩ P a b hP (hc ⟨p, hp.out⟩)
  obtain ⟨m, hm⟩ := RationalIntegrality.exists_int_of_forall_norm_le_one a
    (fun p hp => (hlocal p hp).1)
  obtain ⟨n, hn⟩ := RationalIntegrality.exists_int_of_forall_norm_le_one b
    (fun p hp => (hlocal p hp).2)
  refine ⟨(m : Integers) + (n : Integers) * zetaInteger, ?_⟩
  rw [hP, ← hm, ← hn]
  simp [zetaInteger]

/-- Being a unit at every finite place is equivalent to being a global integer unit. -/
theorem finite_compact_iff_integer_unit (P : Points) :
    finiteDiagonal P ∈ finiteCompact ↔ ∃ u : Integersˣ, rationalUnit u = P := by
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := exists_integer_parameter P hc
    obtain ⟨y, hy⟩ := exists_integer_parameter P⁻¹
      (by simpa only [map_inv] using finiteCompact.inv_mem hc)
    let u : Integersˣ := {
      val := x
      inv := y
      val_inv := by
        apply RingOfIntegers.coe_injective
        change (x : E) * (y : E) = 1
        rw [hx, hy, map_inv]
        exact (parameterEquiv P).val_inv
      inv_val := by
        apply RingOfIntegers.coe_injective
        change (y : E) * (x : E) = 1
        rw [hx, hy, map_inv]
        exact (parameterEquiv P).inv_val }
    refine ⟨u, ?_⟩
    apply parameterEquiv.injective
    change parameterEquiv (parameterEquiv.symm (Units.map (algebraMap Integers E) u)) = _
    rw [MulEquiv.apply_symm_apply]
    exact Units.ext hx
  · rintro ⟨u, rfl⟩
    exact (diagonal_rationalUnit_mem_maximalCompact u).2

theorem maximalCompact_iff_integer_unit (P : Points) :
    diagonal P ∈ maximalCompact ↔ ∃ u : Integersˣ, rationalUnit u = P := by
  constructor
  · intro h
    exact (finite_compact_iff_integer_unit P).mp h.2
  · rintro ⟨u, rfl⟩
    exact diagonal_rationalUnit_mem_maximalCompact u

def integerUnitsToRationalCompact : Integersˣ →* rationalCompact where
  toFun u := ⟨⟨diagonal (rationalUnit u), diagonal_rationalUnit_mem_maximalCompact u⟩,
    ⟨rationalUnit u, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' u v := Subtype.ext (Subtype.ext (by simp))

theorem integerUnitsToRationalCompact_bijective : Function.Bijective integerUnitsToRationalCompact := by
  constructor
  · intro u v h
    exact rationalUnit_injective (diagonal_injective
      (congrArg (fun x : rationalCompact => (x.val : AdelicData.Points)) h))
  · intro x
    obtain ⟨P, hP⟩ := x.property
    have hc : diagonal P ∈ maximalCompact := hP ▸ x.val.property
    obtain ⟨u, hu⟩ := (maximalCompact_iff_integer_unit P).mp hc
    refine ⟨u, Subtype.ext (Subtype.ext ?_)⟩
    change diagonal (rationalUnit u) = x.val
    rw [hu, hP]
    rfl

/-- The paper's `μmax` is the actual group of global integer units. -/
def integerUnitsEquivRationalCompact : Integersˣ ≃* rationalCompact :=
  MulEquiv.ofBijective integerUnitsToRationalCompact integerUnitsToRationalCompact_bijective

theorem card_rationalCompact : Nat.card rationalCompact = 6 :=
  (Nat.card_congr integerUnitsEquivRationalCompact.symm.toEquiv).trans card_units

end Cubic.PoissonSummation.RationalCompactIntegers
