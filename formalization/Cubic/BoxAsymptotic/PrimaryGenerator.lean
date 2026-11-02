import Cubic.BoxAsymptotic.AngularLocalData

/-! The canonical primary generator of an Eisenstein ideal prime to three.
This connects the element sums used for `eq:Fk` with genuine ideal characters;
no formula for an L-function is built into the definitions. -/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimaryGenerator

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.QuadraticCorrespondence

abbrev ResidueRing := CyclotomicRamifiedReduction.ResidueRing

/-- Primary means congruent to one modulo `3𝒪`. -/
def IsPrimary (x : Integers) : Prop := reduction x = 1

theorem reduction_coord (p : ℤ × ℤ) :
    reduction (coord p) = (p.1 : ResidueRing) + p.2 * CyclotomicRamifiedReduction.residueZeta := by
  simp [coord]

theorem isPrimary_coord (p : ℤ × ℤ) :
    IsPrimary (coord p) ↔ p.1 ≡ 1 [ZMOD 3] ∧ (3 : ℤ) ∣ p.2 := by
  rw [IsPrimary, reduction_coord]
  have h : ((p.1 : ResidueRing) + p.2 * CyclotomicRamifiedReduction.residueZeta = 1) ↔
      (p.1 : ZMod 3) = 1 ∧ (p.2 : ZMod 3) = 0 := by
    simp only [TrivSqZeroExt.ext_iff]
    simp [CyclotomicRamifiedReduction.residueZeta]
    intro hb
    simp [hb]
  rw [h, Cubic.Counting.TraceZeroLattice.dvd_three_iff]
  exact and_congr (by simpa using (ZMod.intCast_eq_intCast_iff p.1 (1 : ℤ) 3)) Iff.rfl

theorem reduction_isUnit (p : ℤ × ℤ)
    (hp : ¬ (3 : ℤ) ∣ p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2) : IsUnit (reduction (coord p)) := by
  rw [reduction_coord, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit ((p.1 : ZMod 3) + p.2 * (1 + 0))
  simp only [add_zero, mul_one]
  apply isUnit_iff_ne_zero.mpr
  have h : ∀ a b : ZMod 3, a ^ 2 - a * b + b ^ 2 ≠ 0 → a + b ≠ 0 := by decide
  have hn : (p.1 : ZMod 3) ^ 2 - p.1 * p.2 + p.2 ^ 2 ≠ 0 := by
    intro hn
    apply hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    simpa using hn
  simpa using h (p.1 : ZMod 3) (p.2 : ZMod 3) hn

theorem exists_primary (I : Ideal Integers) (hI : ¬ 3 ∣ Ideal.absNorm I) :
    ∃ x : Integers, Ideal.span {x} = I ∧ IsPrimary x := by
  obtain ⟨p, hp⟩ := coord_surjective (Cubic.Counting.EisensteinNormCount.gen I)
  have hn : ¬ (3 : ℤ) ∣ p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := by
    intro hn
    apply hI
    have he : Ideal.absNorm I = (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2).natAbs := by
      rw [← span_gen I, ← hp, Ideal.absNorm_span_singleton, norm_coord]
    rw [he]
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hn
  obtain ⟨u, hu⟩ := reduction_isUnit p hn
  obtain ⟨v, hv⟩ := reductionUnits_surjective u
  refine ⟨coord p * (v⁻¹ : Integersˣ), ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_right_unit (v⁻¹).isUnit, hp, span_gen]
  · change reduction (coord p * (v⁻¹ : Integersˣ)) = 1
    rw [map_mul, ← hu]
    have hv' := congrArg Units.val (map_inv reductionUnits v)
    change reduction (↑(v⁻¹)) = ↑((reductionUnits v)⁻¹) at hv'
    rw [hv', hv]
    exact u.val_inv

theorem unique {x y : Integers} (hx : IsPrimary x) (hy : IsPrimary y)
    (hI : Ideal.span {x} = Ideal.span {y}) : x = y := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hI
  have hr := congrArg reduction hu
  rw [map_mul, hx, hy, one_mul] at hr
  have hu1 : u = 1 := (reductionUnits_eq_one_iff u).mp (Units.ext hr)
  simpa [hu1] using hu

/-- Choose the primary generator when it exists, and zero otherwise. Existence and
uniqueness are proved for every ideal prime to three. -/
def generator (I : Ideal Integers) : Integers := by
  classical
  exact if h : ∃ x : Integers, Ideal.span {x} = I ∧ IsPrimary x then h.choose else 0

theorem generator_spec (I : Ideal Integers) (hI : ¬ 3 ∣ Ideal.absNorm I) :
    Ideal.span {generator I} = I ∧ IsPrimary (generator I) := by
  rw [generator, dif_pos (exists_primary I hI)]
  exact (exists_primary I hI).choose_spec

theorem generator_eq {I : Ideal Integers} (hI : ¬ 3 ∣ Ideal.absNorm I)
    {x : Integers} (hx : IsPrimary x) (hspan : Ideal.span {x} = I) : generator I = x :=
  unique (generator_spec I hI).2 hx ((generator_spec I hI).1.trans hspan.symm)

theorem generator_mul {I J : Ideal Integers}
    (hI : ¬ 3 ∣ Ideal.absNorm I) (hJ : ¬ 3 ∣ Ideal.absNorm J) :
    generator (I * J) = generator I * generator J := by
  have hIJ : ¬ 3 ∣ Ideal.absNorm (I * J) := by
    rw [map_mul]
    exact fun h => (Nat.prime_three.dvd_mul.mp h).elim hI hJ
  apply generator_eq hIJ
  · change reduction (generator I * generator J) = 1
    rw [map_mul, (generator_spec I hI).2, (generator_spec J hJ).2, one_mul]
  · rw [← Ideal.span_singleton_mul_span_singleton, (generator_spec I hI).1,
      (generator_spec J hJ).1]

end Cubic.BoxAsymptotic.PrimaryGenerator
