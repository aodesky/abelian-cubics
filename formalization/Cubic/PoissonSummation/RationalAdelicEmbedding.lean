import Cubic.PoissonSummation.AdelicData
import Cubic.ToricHeights.QuotientCompactCriterion

/-!
# The rational diagonal in the original adelic point group

Base change is composition of the original invariant-ring point with the
coefficient embedding. Almost-everywhere compactness follows from integrality
of the original cubic coefficients of a rational point and its inverse:
only finitely many primes divide their denominators. No product formula or
triviality of an adelic character is assumed in this construction.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalAdelicEmbedding

open Filter
open Cubic.QuadraticCorrespondence CyclotomicTorusGalois RationalQuotientGroup
open DescendedCoefficients Cubic.ToricHeights
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open scoped RationalQuotientGroup RestrictedProduct

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

abbrev Points := quotientFixedRing →ₐ[ℚ] ℚ

/-- Scalar extension of an original rational quotient point. -/
def baseChange (A : Type*) [CommRing A] [Algebra ℚ A] :
    Points →* (quotientFixedRing →ₐ[ℚ] A) := mapPoint ℚ (Algebra.ofId ℚ A)

@[simp]
theorem baseChange_apply (A : Type*) [CommRing A] [Algebra ℚ A]
    (P : Points) (b : quotientFixedRing) :
    baseChange A P b = algebraMap ℚ A (P b) := rfl

/-- The local-data bundle uses the original quotient group at the indexed prime. -/
def originalEquiv (p : Nat.Primes) :
    (family p).Carrier ≃* (quotientFixedRing →ₐ[ℚ] ℚ_[p]) := by
  by_cases hs : (p : ℕ) % 3 = 1
  · rw [family_split ⟨p, hs⟩]
    exact MulEquiv.refl _
  by_cases hi : (p : ℕ) % 3 = 2
  · rw [family_inert ⟨p, hi⟩]
    exact MulEquiv.refl _
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    have hp : p = primeThree := Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst p
    exact MulEquiv.refl _

/-- The rational point in the local group used by the Fourier calculation. -/
def localPoint (p : Nat.Primes) : Points →* (family p).Carrier :=
  (originalEquiv p).symm.toMonoidHom.comp (baseChange ℚ_[p])

theorem originalEquiv_localPoint (p : Nat.Primes) (P : Points) :
    originalEquiv p (localPoint p P) = (Algebra.ofId ℚ ℚ_[p]).comp P :=
  (originalEquiv p).apply_symm_apply _

/-- A rational function value is integral away from the finitely many denominator primes. -/
theorem eventually_norm_rat_le_one (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, ‖(q : ℚ_[p])‖ ≤ 1 := by
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ q.den}.Finite :=
    (Set.finite_Iic q.den).preimage Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  exact Padic.norm_rat_le_one (fun hd => hp (Nat.le_of_dvd q.den_pos hd))

theorem eventually_coefficient_integral (P : Points) :
    ∀ᶠ p : Nat.Primes in cofinite,
      baseChange ℚ_[p] P ∈ QuotientLocalIntegrality.coefficientLocus p := by
  filter_upwards [eventually_norm_rat_le_one (P linearCoefficient),
    eventually_norm_rat_le_one (P constantCoefficient)] with p ha hb
  exact ⟨ha, hb⟩

private theorem transport_equiv_property
    {A : Type*} [Mul A]
    (P : (D : CubicTargets.PoissonSummation.FiniteFourierProduct.LocalData) →
      (D.Carrier ≃* A) → Prop)
    {D F : CubicTargets.PoissonSummation.FiniteFourierProduct.LocalData}
    (h : D = F) (e : F.Carrier ≃* A) (he : P F e) :
    P D ((congrArg (fun D => D.Carrier ≃* A) h).mpr e) := by
  subst F
  exact he

/-- The two coefficient cutoffs force maximal-compact membership away from three. -/
theorem localPoint_mem_compact_of_integral (p : Nat.Primes) (hp : p ≠ primeThree)
    (P : Points)
    (hP : baseChange ℚ_[p] P ∈ QuotientLocalIntegrality.coefficientLocus p)
    (hPi : baseChange ℚ_[p] P⁻¹ ∈ QuotientLocalIntegrality.coefficientLocus p) :
    localPoint p P ∈ (family p).maxCompact := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    have h := QuotientCompactCriterion.split_mem_compact_of_integral p
      (baseChange ℚ_[p] P) hP (by simpa only [map_inv] using hPi)
    change (originalEquiv p).symm (baseChange ℚ_[p] P) ∈ (family p).maxCompact
    simp only [originalEquiv, dif_pos hs]
    exact transport_equiv_property (fun D e => e.symm (baseChange ℚ_[p] P) ∈ D.maxCompact)
      (family_split ⟨p, hs⟩) (MulEquiv.refl _) h
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    have h := QuotientCompactCriterion.inert_mem_compact_of_integral p
      (baseChange ℚ_[p] P) hP (by simpa only [map_inv] using hPi)
    change (originalEquiv p).symm (baseChange ℚ_[p] P) ∈ (family p).maxCompact
    simp only [originalEquiv, dif_neg hs, dif_pos hi]
    exact transport_equiv_property (fun D e => e.symm (baseChange ℚ_[p] P) ∈ D.maxCompact)
      (family_inert ⟨p, hi⟩) (MulEquiv.refl _) h
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    exact (hp (Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)))).elim

/-- Every original rational point is in the finite maximal compacts almost everywhere. -/
theorem eventually_mem_compact (P : Points) :
    ∀ᶠ p : Nat.Primes in cofinite, localPoint p P ∈ (family p).maxCompact := by
  filter_upwards [eventually_coefficient_integral P, eventually_coefficient_integral P⁻¹,
    Filter.eventually_cofinite_ne primeThree] with p hP hPi hp
  exact localPoint_mem_compact_of_integral p hp P hP hPi

/-- The actual finite rational diagonal; its restricted-product condition is proved above. -/
def finiteDiagonal : Points →* FiniteAdelicData.Points where
  toFun P := ⟨fun p => localPoint p P, eventually_mem_compact P⟩
  map_one' := by ext p; exact map_one (localPoint p)
  map_mul' P Q := by ext p; exact map_mul (localPoint p) P Q

@[simp]
theorem finiteDiagonal_apply (P : Points) (p : Nat.Primes) :
    finiteDiagonal P p = localPoint p P := rfl

/-- The rational diagonal in the original real group times the finite restricted product. -/
def diagonal : Points →* AdelicData.Points := (baseChange ℝ).prod finiteDiagonal

theorem diagonal_injective : Function.Injective diagonal := by
  intro P Q h
  have hreal : baseChange ℝ P = baseChange ℝ Q := congrArg Prod.fst h
  apply AlgHom.ext
  intro b
  exact (algebraMap ℚ ℝ).injective (congrArg (fun f => f b) hreal)

end Cubic.PoissonSummation.RationalAdelicEmbedding
