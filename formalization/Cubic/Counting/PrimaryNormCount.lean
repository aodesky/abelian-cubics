import Cubic.Counting.EisensteinNormCount
import Cubic.PoissonSummation.CyclotomicIntegerUnits

/-!
# Generators congruent to one modulo `1 - ζ`

Supporting arithmetic for `thm:exactFormula`. The paper: "Since `3 ∤ n`, an ideal of
norm `n` has six generators `±ζʲθ`, and since `ζ ≡ 1 (mod 1-ζ)`, exactly three of them,
`θ, ζθ, ζ²θ`, are congruent to `1`."

Reduction modulo `1 - ζ` is the ring map `residue : 𝓞_E → ℤ/3` sending `ζ ↦ 1`, so
`residue (u + vζ) = u + v`. Since `(u+v)² ≡ u² - uv + v² (mod 3)`, a generator of an
ideal of norm prime to `3` has residue `±1`, so `±` of it is congruent to one
(`exists_primary_generator`). The six generators of `(θ)` are `±ζʲθ`; since
`residue (-1) = -1` and `residue ζ = 1`, the ones congruent to one when `θ` is are
`θ, ζθ, ζ²θ` (`primary_generator_iff`).
-/

noncomputable section

namespace Cubic.Counting.PrimaryNormCount

open Cubic.PoissonSummation Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount Cubic.Counting.EisensteinIdealCount

/-- Reduction modulo the prime `1 - ζ` above `3`. -/
def residue : Integers →+* ZMod 3 :=
  (TrivSqZeroExt.fstHom (ZMod 3) (ZMod 3) (ZMod 3)).toRingHom.comp reduction

theorem residue_zeta : residue zetaInteger = 1 := by
  simp only [residue, RingHom.comp_apply, reduction_zeta]
  rfl

/-- `ζ ≡ 1 (mod 1 - ζ)`, so `u + vζ ≡ u + v`. -/
theorem residue_coord (p : ℤ × ℤ) : residue (coord p) = ((p.1 + p.2 : ℤ) : ZMod 3) := by
  simp [coord, residue_zeta]

/-- `(u + v)² ≡ u² - uv + v² (mod 3)`. -/
theorem residue_sq (p : ℤ × ℤ) :
    residue (coord p) ^ 2 = ((p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 : ℤ) : ZMod 3) := by
  rw [residue_coord]
  have h3 : (3 : ZMod 3) = 0 := by decide
  push_cast
  linear_combination ((p.1 : ZMod 3) * p.2) * h3

theorem residue_ne_zero_of_norm (p : ℤ × ℤ) {K : ℕ} (hK : ¬ 3 ∣ K)
    (hp : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K) : residue (coord p) ≠ 0 := by
  intro h0
  have h := residue_sq p
  rw [h0, hp] at h
  have : ((K : ℤ) : ZMod 3) = 0 := by simpa using h.symm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  exact hK (by exact_mod_cast this)

theorem eq_one_or_neg_one (t : ZMod 3) (ht : t ≠ 0) : t = 1 ∨ t = -1 := by
  revert t; decide

/-- The integer pairs `(u, v)` with `u² - uv + v² = K` and `u + v ≡ 1 (mod 3)`,
i.e. the elements `θ = u + vζ` of norm `K` with `θ ≡ 1 (mod 1 - ζ)`. -/
def primarySet (K : ℤ) : Set (ℤ × ℤ) :=
  {p | p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K ∧ (3 : ℤ) ∣ 1 - p.1 - p.2}

theorem dvd_iff_residue (p : ℤ × ℤ) : (3 : ℤ) ∣ 1 - p.1 - p.2 ↔ residue (coord p) = 1 := by
  have h := ZMod.intCast_zmod_eq_zero_iff_dvd (1 - p.1 - p.2) 3
  push_cast at h
  rw [residue_coord, ← h]
  push_cast
  constructor <;> intro h <;> linear_combination -h

theorem residue_gen {K : ℕ} (I : {I : Ideal Integers // Ideal.absNorm I = K}) (hK : ¬ 3 ∣ K) :
    residue (gen I.1) = 1 ∨ residue (gen I.1) = -1 := by
  obtain ⟨p, hp⟩ := coord_surjective (gen I.1)
  have hn := I.2
  rw [← span_gen I.1, ← hp, Ideal.absNorm_span_singleton, norm_coord] at hn
  have hp' : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K := by
    rw [← hn, Int.natAbs_of_nonneg (normForm_nonneg _ _)]
  rw [← hp]
  exact eq_one_or_neg_one _ (residue_ne_zero_of_norm p hK hp')

/-- Since `3 ∤ K`, some generator of an ideal of norm `K` is congruent to one. -/
theorem exists_primary_generator {K : ℕ} (I : {I : Ideal Integers // Ideal.absNorm I = K})
    (hK : ¬ 3 ∣ K) : ∃ θ : Integers, Ideal.span {θ} = I.1 ∧ residue θ = 1 := by
  rcases residue_gen I hK with h | h
  · exact ⟨gen I.1, span_gen I.1, h⟩
  · exact ⟨-gen I.1, by rw [Ideal.span_singleton_neg, span_gen], by rw [map_neg, h, neg_neg]⟩

/-- The paper: "an ideal of norm `n` has six generators `±ζʲθ`, and since `ζ ≡ 1`,
exactly three of them, `θ, ζθ, ζ²θ`, are congruent to `1`." For `θ ≡ 1`, a generator
`θ'` of `(θ)` with `θ' ≡ 1` is `ζʲθ`. -/
theorem primary_generator_iff {θ θ' : Integers} (hθ : residue θ = 1) (hθ' : residue θ' = 1) :
    Ideal.span {θ'} = Ideal.span {θ} ↔ ∃ j : ZMod 3, θ' = zetaInteger ^ j.val * θ := by
  constructor
  · intro h
    -- the six generators of `(θ)` are `θu` for the six units `u = ±ζʲ`
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp h).symm
    have hres : residue u = 1 := by
      have := congrArg residue hu
      rwa [map_mul, hθ, hθ', one_mul] at this
    have h3 : (-1 : ZMod 3) ≠ 1 := by decide
    rcases units_exhaustive u with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by rw [← hu]; simp⟩
    · simp at hres; exact absurd hres h3
    · exact ⟨1, by rw [← hu, coe_zetaUnit, mul_comm, show (1 : ZMod 3).val = 1 from rfl, pow_one]⟩
    · simp [coe_zetaUnit, residue_zeta] at hres; exact absurd hres h3
    · exact ⟨2, by rw [← hu, Units.val_pow_eq_pow_val, coe_zetaUnit, mul_comm]; rfl⟩
    · simp [coe_zetaUnit, residue_zeta] at hres; exact absurd hres h3
  · rintro ⟨j, rfl⟩
    rw [mul_comm, ← coe_zetaUnit, ← Units.val_pow_eq_pow_val,
      Ideal.span_singleton_mul_right_unit (zetaUnit ^ j.val).isUnit]

end Cubic.Counting.PrimaryNormCount
