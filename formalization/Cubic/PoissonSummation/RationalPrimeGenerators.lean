import Cubic.PoissonSummation.RationalPrincipalGenerators
import Cubic.ToricHeights.RamifiedLocalValuation

/-!
# Rational generators supported at one finite prime

At inert primes the generator is the scalar prime. At three it is `ζ-1`,
with integral valuation one and height coordinate one-half. At split primes
the principal ideal generator has valuations `(1,0)`; the scalar prime has
valuations `(1,1)`. Their integer powers realize both split valuations.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalPrimeGenerators

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicField CyclotomicIntegerUnits RationalPrincipalGenerators
open RationalAdelicEmbedding QuotientFiniteFourierProduct
open Cubic.OrbitParametrization
open scoped RationalQuotientGroup

def supportedAt (p : ℕ) : Subgroup Points where
  carrier := {P | ∀ q : Nat.Primes, (q : ℕ) ≠ p → localPoint q P ∈ (family q).maxCompact}
  one_mem' := by intro q _; rw [map_one]; exact (family q).maxCompact.one_mem
  mul_mem' := by
    intro P Q hP hQ q hq
    rw [map_mul]
    exact (family q).maxCompact.mul_mem (hP q hq) (hQ q hq)
  inv_mem' := by
    intro P hP q hq
    rw [map_inv]
    exact (family q).maxCompact.inv_mem (hP q hq)

def scalarPoint (p : ℕ) (hp : p ≠ 0) : Points := point (p : Integers) (by exact_mod_cast hp)

theorem scalarPoint_supported (p : ℕ) (hp : p.Prime) :
    scalarPoint p hp.ne_zero ∈ supportedAt p :=
  localPoint_compact_of_dvd_prime p hp _ _ (dvd_refl _)

variable (p : ℕ) [Fact p.Prime]

theorem split_scalarPoint [Fact (p % 3 = 1)] :
    SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p]
      (scalarPoint p (Fact.out : p.Prime).ne_zero)) =
      (PadicMultiplicative.uniformizer p, PadicMultiplicative.uniformizer p) := by
  apply Prod.ext <;> apply Units.ext
  · rw [scalarPoint, split_first_point, map_natCast]; rfl
  · rw [scalarPoint, split_second_point, map_natCast]; rfl

theorem inert_scalarPoint [Fact (p % 3 = 2)] :
    InertQuotientLogarithm.localPoint p (baseChange ℚ_[p]
      (scalarPoint p (Fact.out : p.Prime).ne_zero)) = InertLocalModel.uniformizer p := by
  apply Units.ext
  rw [scalarPoint, inert_point, map_natCast]
  simp [InertLocalModel.uniformizer, PadicMultiplicative.uniformizer]

section Split
variable [Fact (p % 3 = 1)]

def splitPoint : Points :=
  point (CyclotomicSplitGenerators.generator p) (CyclotomicSplitGenerators.generator_ne_zero p)

theorem splitPoint_supported : splitPoint p ∈ supportedAt p := by
  letI : IsPrincipalIdealRing Integers := integers_principal
  apply localPoint_compact_of_dvd_prime p (Fact.out : p.Prime)
  exact IsBezout.gcd_dvd_left (p : Integers)
    (zetaInteger - CyclotomicSplitGenerators.residue p)

theorem splitPoint_first_norm :
    ‖((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] (splitPoint p))).1 : ℚ_[p])‖ =
      (p : ℝ)⁻¹ := by
  rw [splitPoint, split_first_point]
  exact CyclotomicSplitGenerators.first_generator_norm p

theorem splitPoint_second_norm :
    ‖((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] (splitPoint p))).2 : ℚ_[p])‖ = 1 := by
  rw [splitPoint, split_second_point]
  exact CyclotomicSplitGenerators.second_generator_norm p

end Split

def ramifiedInteger : Integers := zetaInteger - 1

theorem ramifiedInteger_dvd_three : ramifiedInteger ∣ (3 : Integers) := by
  refine ⟨-zetaInteger - 2, ?_⟩
  apply (show Function.Injective (algebraMap Integers E) from Subtype.val_injective)
  change (3 : E) = (zeta - 1) * (-zeta - 2)
  linear_combination zeta_relation

theorem ramifiedInteger_ne_zero : ramifiedInteger ≠ 0 := by
  intro h
  have hd := ramifiedInteger_dvd_three
  rw [h, zero_dvd_iff] at hd
  exact (by norm_num : (3 : Integers) ≠ 0) hd

def ramifiedPoint : Points := point ramifiedInteger ramifiedInteger_ne_zero

theorem ramifiedPoint_supported : ramifiedPoint ∈ supportedAt 3 :=
  localPoint_compact_of_dvd_prime 3 Nat.prime_three _ _ ramifiedInteger_dvd_three

theorem ramifiedPoint_local :
    RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] ramifiedPoint) =
      RamifiedLocalModel.ramifiedParameter := by
  apply Units.ext
  rw [ramifiedPoint, ramified_point]
  change toLocalField (zeta - 1) = CyclotomicRamifiedField.zeta - 1
  rw [map_sub, map_one, toLocalField_zeta]

end Cubic.PoissonSummation.RationalPrimeGenerators
