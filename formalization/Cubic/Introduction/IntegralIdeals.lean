import Cubic.Introduction.IntegralEisenstein

/-! Primary generators identify the actual cube-norm ideals prime to three.
The congruence condition is checked against the ideal `3𝒪_E`. -/

noncomputable section

namespace Cubic.Introduction.IntegralIdeals

open EisensteinPointData IntegralEisenstein
open Cubic.QuadraticCorrespondence CyclotomicField
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.PrimaryGenerator Cubic.BoxAsymptotic.HeckeModulus
open Cubic.Counting.EisensteinNormCount

theorem norm_span (β : Integers) :
    (Ideal.absNorm (Ideal.span {β}) : ℚ) = Algebra.norm ℚ (β : E) := by
  obtain ⟨p, rfl⟩ := coord_surjective β
  rw [Ideal.absNorm_span_singleton, norm_coord, norm_coord_rational]
  exact congrArg (fun z : ℤ => (z : ℚ))
    (Int.natAbs_of_nonneg (normForm_nonneg p.1 p.2))

def toIdeal (β : PrimaryCubes) : CubeIdeals :=
  ⟨Ideal.span {β.1}, primary_norm_prime_to_three β.2.1, by
    obtain ⟨M, hM⟩ := β.2.2
    refine ⟨M, ?_⟩
    have h := norm_span β.1
    rw [hM] at h
    exact_mod_cast h⟩

theorem toIdeal_injective : Function.Injective toIdeal := by
  intro β γ h
  exact Subtype.ext (unique β.2.1 γ.2.1 (congrArg Subtype.val h))

theorem toIdeal_surjective : Function.Surjective toIdeal := by
  intro I
  obtain ⟨M, hM⟩ := I.2.2
  have hg := generator_spec I.1 I.2.1
  have hn : Algebra.norm ℚ (generator I.1 : E) = (M : ℚ) ^ 3 := by
    rw [← norm_span, hg.1, hM]
    simp
  exact ⟨⟨generator I.1, hg.2, M, hn⟩, Subtype.ext hg.1⟩

def idealEquiv : PrimaryCubes ≃ CubeIdeals :=
  Equiv.ofBijective toIdeal ⟨toIdeal_injective, toIdeal_surjective⟩

theorem ideal_condition (I : Ideal Integers) :
    (¬ 3 ∣ Ideal.absNorm I) ↔ I ⊔ Ideal.span {(3 : Integers)} = ⊤ := by
  constructor
  · intro hI
    obtain ⟨β, hβ, hp⟩ := exists_primary I hI
    rw [← hβ, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    obtain ⟨c, hc⟩ := (isPrimary_iff β).mp hp
    refine ⟨1, -c, ?_⟩
    linear_combination hc
  · intro hI
    rw [← span_gen I, ← Ideal.isCoprime_iff_sup_eq,
      Ideal.isCoprime_span_singleton_iff] at hI
    obtain ⟨a, b, hab⟩ := hI
    have hu : IsUnit (reduction (gen I)) := by
      apply isUnit_iff_exists_inv'.mpr
      refine ⟨reduction a, ?_⟩
      have h := congrArg reduction hab
      simpa only [map_add, map_mul, map_ofNat, map_one,
        show (3 : Cubic.BoxAsymptotic.PrimaryGenerator.ResidueRing) = 0 by decide,
        mul_zero, add_zero] using h
    have h := (reduction_isUnit_iff_norm (gen I)).mp hu
    simpa only [span_gen] using h

end Cubic.Introduction.IntegralIdeals
