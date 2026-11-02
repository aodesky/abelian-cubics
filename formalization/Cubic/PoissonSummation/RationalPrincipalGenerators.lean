import Cubic.PoissonSummation.CyclotomicSplitGenerators
import Cubic.PoissonSummation.RationalAdelicEmbedding
import Cubic.PoissonSummation.RationalUnitReduction

/-!
# Principal generators as original rational torus points

A nonzero global integer gives a point through the proved rational parameter
equivalence. Its local parameters are obtained by the specified scalar-extension
maps. Divisors of a rational prime are units at every other finite prime; this
is proved on the original local point groups, including the ramified group.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalPrincipalGenerators

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicField CyclotomicIntegerUnits CyclotomicPrincipalGenerators
open RationalParameterBaseChange RationalAdelicEmbedding
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open scoped RationalQuotientGroup TensorProduct

def point (a : Integers) (ha : a ≠ 0) : Points :=
  parameterEquiv.symm (Units.mk0 (a : E) (by
    intro h
    exact ha (Subtype.ext h)))

@[simp]
theorem parameter_point (a : Integers) (ha : a ≠ 0) :
    (parameterEquiv (point a ha) : E) = a := by simp [point]

def integerRealization (A : Type*) [CommRing A] [Algebra ℚ A]
    {B : Type*} [CommRing B] (f : E ⊗[ℚ] A →+* B) : Integers →+* B :=
  f.comp ((fieldInclusion A).toRingHom.comp (algebraMap Integers E))

theorem realization_point (A : Type*) [CommRing A] [Algebra ℚ A]
    {B : Type*} [CommRing B] (f : E ⊗[ℚ] A →+* B) (a : Integers) (ha : a ≠ 0) :
    f (RationalQuotientGroup.quotientRestrictionScalarsMulEquiv A
      (baseChange A (point a ha))) = integerRealization A f a := by
  change f (RationalQuotientGroup.quotientRestrictionScalarsMulEquiv A
    ((Algebra.ofId ℚ A).comp (point a ha))) = _
  rw [parameter_baseChange_val, parameter_point]
  rfl

theorem split_first_point (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (a : Integers) (ha : a ≠ 0) :
    ((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] (point a ha))).1 : ℚ_[p]) =
      CyclotomicSplitGenerators.firstEmbedding p a :=
  realization_point ℚ_[p] (SplitQuotientLogarithm.place p) a ha

theorem split_second_point (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (a : Integers) (ha : a ≠ 0) :
    ((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] (point a ha))).2 : ℚ_[p]) =
      CyclotomicSplitGenerators.secondEmbedding p a :=
  realization_point ℚ_[p] (SplitQuotientLogarithm.secondPlace p) a ha

def inertEmbedding (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)] :
    Integers →+* CyclotomicInertField.Extension p :=
  integerRealization ℚ_[p] (InertQuotientLogarithm.place p).toRingHom

theorem inert_point (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (a : Integers) (ha : a ≠ 0) :
    (InertQuotientLogarithm.localPoint p (baseChange ℚ_[p] (point a ha)) :
      CyclotomicInertField.Extension p) = inertEmbedding p a :=
  realization_point ℚ_[p] (InertQuotientLogarithm.place p).toRingHom a ha

theorem ramified_point (a : Integers) (ha : a ≠ 0) :
    (RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] (point a ha)) :
      CyclotomicRamifiedField.Extension) = toLocalField (a : E) := by
  rw [RationalUnitReduction.ramifiedParameter_baseChange]
  change toLocalField (parameterEquiv (point a ha) : E) = _
  rw [parameter_point]

/-- A global divisor of an element which is locally a unit is locally a unit. -/
theorem norm_image_of_dvd {F : Type*} [NormedField F] [IsUltrametricDist F]
    (f : Integers →+* F) {a b : Integers} (hab : a ∣ b) (hb : ‖f b‖ = 1) :
    ‖f a‖ = 1 := by
  obtain ⟨c, rfl⟩ := hab
  apply le_antisymm (norm_integer_image f a)
  calc
    1 = ‖f a‖ * ‖f c‖ := by simpa only [map_mul, norm_mul] using hb.symm
    _ ≤ ‖f a‖ * 1 := mul_le_mul_of_nonneg_left (norm_integer_image f c) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_prime_at_other (p q : ℕ) [Fact q.Prime] (hp : p.Prime) (hpq : q ≠ p) :
    ‖(p : ℚ_[q])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  exact (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (fun hd => hpq ((hp.dvd_iff_eq (Fact.out : q.Prime).ne_one).mp hd).symm)

theorem padic_compact_of_norm_one (p : ℕ) [Fact p.Prime] (x : ℚ_[p]ˣ)
    (hx : ‖(x : ℚ_[p])‖ = 1) :
    x ∈ Cubic.OrbitParametrization.PadicMultiplicative.compactUnits p := by
  rw [Cubic.OrbitParametrization.PadicMultiplicative.mem_compactUnits,
    Units.val_inv_eq_inv_val, norm_inv, hx]
  norm_num

private theorem transport_compact_membership {A : Type*} [Mul A]
    {D F : LocalData} (h : D = F) (e : F.Carrier ≃* A) (x : A) :
    ((congrArg (fun D => D.Carrier ≃* A) h).mpr e).symm x ∈ D.maxCompact ↔
      e.symm x ∈ F.maxCompact := by subst F; rfl

/-- The required support statement for each principal generator, on the actual local groups. -/
theorem localPoint_compact_of_dvd_prime (p : ℕ) (hp : p.Prime)
    (a : Integers) (ha : a ≠ 0) (hap : a ∣ (p : Integers))
    (q : Nat.Primes) (hqp : (q : ℕ) ≠ p) :
    localPoint q (point a ha) ∈ (family q).maxCompact := by
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hnorm := norm_prime_at_other p q hp hqp
  change (originalEquiv q).symm (baseChange ℚ_[q] (point a ha)) ∈ (family q).maxCompact
  by_cases hs : (q : ℕ) % 3 = 1
  · letI : Fact ((q : ℕ) % 3 = 1) := ⟨hs⟩
    simp only [originalEquiv, dif_pos hs]
    apply (transport_compact_membership (family_split ⟨q, hs⟩) (MulEquiv.refl _) _).mpr
    change SplitQuotientLogarithm.localPoint q (baseChange ℚ_[q] (point a ha)) ∈
      SplitLocalModel.compactUnits q
    constructor
    · apply padic_compact_of_norm_one
      rw [split_first_point]
      exact norm_image_of_dvd _ hap (by simpa only [map_natCast] using hnorm)
    · apply padic_compact_of_norm_one
      rw [split_second_point]
      exact norm_image_of_dvd _ hap (by simpa only [map_natCast] using hnorm)
  by_cases hi : (q : ℕ) % 3 = 2
  · letI : Fact ((q : ℕ) % 3 = 2) := ⟨hi⟩
    simp only [originalEquiv, dif_neg hs, dif_pos hi]
    apply (transport_compact_membership (family_inert ⟨q, hi⟩) (MulEquiv.refl _) _).mpr
    change InertQuotientLogarithm.localPoint q (baseChange ℚ_[q] (point a ha)) ∈
      CyclotomicInertField.compactUnits q
    rw [CyclotomicInertField.mem_compactUnits_iff_norm_one, inert_point]
    apply norm_image_of_dvd _ hap
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[q] (CyclotomicInertField.Extension q)),
      CyclotomicInertField.norm_algebraMap]
    exact hnorm
  · have h0 : (q : ℕ) % 3 = 0 := by omega
    have hq : q = primeThree := Subtype.ext
      ((q.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst q
    change RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] (point a ha)) ∈
      CyclotomicRamifiedField.compactUnits
    rw [CyclotomicRamifiedField.mem_compactUnits_iff_norm_one, ramified_point]
    apply norm_image_of_dvd (toLocalField.toRingHom.comp (algebraMap Integers E)) hap
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[3] CyclotomicRamifiedField.Extension),
      CyclotomicRamifiedField.norm_algebraMap]
    exact hnorm

end Cubic.PoissonSummation.RationalPrincipalGenerators
