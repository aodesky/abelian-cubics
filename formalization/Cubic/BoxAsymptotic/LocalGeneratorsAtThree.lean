import Cubic.BoxAsymptotic.LocalNormAtThree
import Cubic.BoxAsymptotic.AngularIdeals

/-! Generator identifications for `lem:local3`: primary lattice elements are
exactly the primary generators of the actual ideals of norm `M³`, and every
element of norm `(3^e M)³` is `u λ^(3e) α` with `α` primary. -/

noncomputable section

namespace Cubic.BoxAsymptotic.LocalGeneratorsAtThree

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularLocalData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.PrimaryGenerator Cubic.BoxAsymptotic.LocalAtThreeData
open Cubic.BoxAsymptotic.LocalNormAtThree Cubic.BoxAsymptotic.ZeroModeMass

@[simp] theorem coord_neg (p : ℤ × ℤ) : coord (-p) = -coord p := by
  simp [coord]
  ring

theorem normSet_iff_absNorm (M : ℕ) (p : ℤ × ℤ) :
    p ∈ normSet ((M : ℤ) ^ 3) ↔ Ideal.absNorm (spanCoord p) = M ^ 3 := by
  rw [spanCoord, Ideal.absNorm_span_singleton, norm_coord]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    change _ = (M : ℤ) ^ 3
    rw [← Int.natAbs_of_nonneg (normForm_nonneg _ _), h]
    simp

/-- The coordinate definition of `𝒫_M` is exactly the ideal-generator definition. -/
theorem primary_iff_ideal {M : ℕ} (hM : ¬ 3 ∣ M) (p : ℤ × ℤ) :
    p ∈ primary M ↔ ∃ I : Ideal Integers,
      Ideal.absNorm I = M ^ 3 ∧ coord p = generator I := by
  constructor
  · intro hp
    exact ⟨spanCoord p, norm_spanCoord hp, (primary_generator_span hM hp).symm⟩
  · rintro ⟨I, hI, hp⟩
    have h3 : ¬ 3 ∣ Ideal.absNorm I := by rw [hI]; exact prime_to_three_cube hM
    refine ⟨(normSet_iff_absNorm M p).mpr ?_, (isPrimary_coord p).mp ?_⟩
    · rw [spanCoord, hp, (generator_spec I h3).1]
      exact hI
    · rw [hp]
      exact (generator_spec I h3).2

/-- The six associates of the primary generators exhaust the unramified norm set. -/
theorem normSet_unit_primary {M : ℕ} (hM : ¬ 3 ∣ M) (p : ℤ × ℤ) :
    p ∈ normSet ((M : ℤ) ^ 3) ↔
      ∃ (u : Integersˣ) (α : ℤ × ℤ), α ∈ primary M ∧ coord p = (u : Integers) * coord α := by
  constructor
  · intro hp
    have hI : spanCoord p ∈ cubeNormIdeals M := (normSet_iff_absNorm M p).mp hp
    rw [← primary_image M hM] at hI
    obtain ⟨α, hα, hspan⟩ := hI
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    exact ⟨u, α, hα, by simpa [mul_comm] using hu.symm⟩
  · rintro ⟨u, α, hα, hp⟩
    apply (normSet_iff_absNorm M p).mpr
    rw [spanCoord, hp, Ideal.span_singleton_mul_left_unit u.isUnit]
    exact norm_spanCoord hα

/-- The actual ring-theoretic generator formula at every ramified power. -/
theorem normSet_generators (e : ℕ) {M : ℕ} (hM : ¬ 3 ∣ M) (p : ℤ × ℤ) :
    p ∈ normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3) ↔
      ∃ (u : Integersˣ) (α : ℤ × ℤ), α ∈ primary M ∧
        coord p = (u : Integers) * lambda ^ (3 * e) * coord α := by
  rw [← iterate_norm_image e M]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨u, α, hα, hq⟩ := (normSet_unit_primary hM q).mp hq
    refine ⟨u, α, hα, ?_⟩
    rw [coord_iterate, hq]
    ring
  · rintro ⟨u, α, hα, hp⟩
    obtain ⟨q, hq⟩ := coord_surjective ((u : Integers) * coord α)
    refine ⟨q, (normSet_unit_primary hM q).mpr ⟨u, α, hα, hq⟩, ?_⟩
    apply coord_injective
    rw [coord_iterate, hq, hp]
    ring

end Cubic.BoxAsymptotic.LocalGeneratorsAtThree
