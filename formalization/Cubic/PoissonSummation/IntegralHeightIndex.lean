import Cubic.PoissonSummation.HeightCountingData
import Cubic.PoissonSummation.AdelicRationalCharacter
import Mathlib.NumberTheory.Padics.WithVal

/-!
# Positive integral indexing of the original rational points

The finite cutoff is equivalent to integrality of the descended cubic
coefficients at every prime. Their rational values are therefore integers.
The original norm character is `1 - 3a`; its positivity at the complex place
makes this a positive integer, congruent to one modulo three. This index is
defined from the coefficient, independently of all Euler-product formulas.
The identification with squared height is proved separately.
-/

noncomputable section

namespace Cubic.PoissonSummation.IntegralHeightIndex

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois DescendedCoefficients
open Cubic.ToricHeights QuotientNormCharacter
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open RationalAdelicEmbedding AdelicHeightZetaData
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open scoped RationalQuotientGroup

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

private theorem transport_locus_property
    {A : Type*} [Mul A] (S : Set A)
    {D F : LocalData} (h : D = F) (e : F.Carrier ≃* A)
    (he : ∀ x, x ∈ F.integralLocus ↔ e x ∈ S) :
    ∀ x, x ∈ D.integralLocus ↔
      ((congrArg (fun D => D.Carrier ≃* A) h).mpr e) x ∈ S := by
  subst F
  exact he

theorem local_integral_iff (p : Nat.Primes) (x : (family p).Carrier) :
    x ∈ (family p).integralLocus ↔
      originalEquiv p x ∈ QuotientLocalIntegrality.coefficientLocus p := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    simp only [originalEquiv, dif_pos hs]
    exact transport_locus_property _ (family_split ⟨p, hs⟩) (MulEquiv.refl _)
      (fun y => by
        change y ∈ QuotientInvariantIntegrality.invariantLocus p ↔ _
        rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus]
        rfl) x
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    simp only [originalEquiv, dif_neg hs, dif_pos hi]
    exact transport_locus_property _ (family_inert ⟨p, hi⟩) (MulEquiv.refl _)
      (fun y => by
        change y ∈ QuotientInvariantIntegrality.invariantLocus p ↔ _
        rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus]
        rfl) x
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    have hp : p = primeThree := Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst p
    change x ∈ QuotientInvariantIntegrality.invariantLocus 3 ↔ _
    rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus]
    rfl

theorem coefficients_padic_integral (P : IntegralRationalPoints) (p : Nat.Primes) :
    ‖(P.val linearCoefficient : ℚ_[p])‖ ≤ 1 ∧
      ‖(P.val constantCoefficient : ℚ_[p])‖ ≤ 1 := by
  have h := (local_integral_iff p (localPoint p P.val)).mp (P.property p)
  rw [originalEquiv_localPoint] at h
  exact h

/-- A rational integral at every finite prime is an integer. -/
theorem rational_isInt_of_local (q : ℚ)
    (hq : ∀ p : Nat.Primes, ‖(q : ℚ_[p])‖ ≤ 1) : q.isInt := by
  suffices q.den = 1 by simp [Rat.isInt, this]
  by_contra hn
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hn
  letI : Fact p.Prime := ⟨hp⟩
  have h := (Padic.norm_rat_le_one_iff_padicValuation_le_one p).mp (hq ⟨p, hp⟩)
  exact (Rat.padicValuation_le_one_iff.mp h) hd

theorem linear_isInt (P : IntegralRationalPoints) : (P.val linearCoefficient).isInt :=
  rational_isInt_of_local _ (fun p => (coefficients_padic_integral P p).1)

theorem constant_isInt (P : IntegralRationalPoints) : (P.val constantCoefficient).isInt :=
  rational_isInt_of_local _ (fun p => (coefficients_padic_integral P p).2)

def index (P : IntegralRationalPoints) : ℕ :=
  (1 - 3 * (P.val linearCoefficient).num).toNat

theorem norm_value_pos (P : RationalAdelicEmbedding.Points) : 0 < (value ℚ P : ℚ) := by
  have h := QuotientNormLogarithm.infinite_value_pos (baseChange ℝ P)
  rw [AdelicRationalCharacter.norm_baseChange, eq_ratCast] at h
  exact_mod_cast h

theorem index_integer_pos (P : IntegralRationalPoints) :
    0 < (1 - 3 * (P.val linearCoefficient).num : ℤ) := by
  have h := norm_value_pos P.val
  rw [value_eq_coefficient, Rat.eq_num_of_isInt (linear_isInt P)] at h
  exact_mod_cast h

theorem index_pos (P : IntegralRationalPoints) : 0 < index P := by
  have h := index_integer_pos P
  dsimp [index]
  omega

theorem index_cast (P : IntegralRationalPoints) :
    (index P : ℤ) = 1 - 3 * (P.val linearCoefficient).num :=
  Int.toNat_of_nonneg (index_integer_pos P).le

theorem norm_value_eq_index (P : IntegralRationalPoints) :
    (value ℚ P.val : ℚ) = (index P : ℚ) := by
  rw [value_eq_coefficient, Rat.eq_num_of_isInt (linear_isInt P)]
  exact_mod_cast (index_cast P).symm

theorem three_not_dvd_index (P : IntegralRationalPoints) : ¬ 3 ∣ index P := by
  intro h
  have hz : (3 : ℤ) ∣ (index P : ℤ) := by exact_mod_cast h
  rw [index_cast] at hz
  have : (3 : ℤ) ∣ 1 := by
    have := dvd_add hz (dvd_mul_right (3 : ℤ) (P.val linearCoefficient).num)
    simpa only [sub_add_cancel] using this
  norm_num at this

end Cubic.PoissonSummation.IntegralHeightIndex
