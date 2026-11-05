import Cubic.Counting.EisensteinNormCount
import Cubic.PoissonSummation.CyclotomicIntegerUnits
import Cubic.Counting.WeightedCount

/-!
# Generators congruent to one modulo `1 - ζ`

Supporting arithmetic for `thm:exactFormula`. The paper: "Since `3 ∤ n`, an ideal of
norm `n` has six generators `±ζʲθ`, and since `ζ ≡ 1 (mod 1-ζ)`, exactly three of them,
`θ, ζθ, ζ²θ`, are congruent to `1`."

Reduction modulo `1 - ζ` is the ring map `residue : 𝓞_E → ℤ/3` sending `ζ ↦ 1`, so
`residue (u + vζ) = u + v`. Since `(u+v)² ≡ u² - uv + v² (mod 3)`, a generator of an
ideal of norm prime to `3` has residue `±1`. The residue of a unit `±ζʲ` is `±1`, so
for each ideal exactly three of its six generators have residue `1`.
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

/-- The six units `±ζʲ` have residue `±1`. -/
theorem residue_unit (u : Integersˣ) : residue u = 1 ∨ residue u = -1 := by
  rcases units_exhaustive u with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [coe_zetaUnit, residue_zeta]

/-- Exactly three units have each residue `±1`: negation exchanges the two classes. -/
theorem card_units_residue (t : ZMod 3) (ht : t = 1 ∨ t = -1) :
    Nat.card {u : Integersˣ // residue u = t} = 3 := by
  have hneg : ∀ u : Integersˣ, residue ((-u : Integersˣ) : Integers) = -residue u := by
    intro u; simp
  let e : {u : Integersˣ // residue u = 1} ≃ {u : Integersˣ // residue u = -1} :=
    { toFun := fun u => ⟨-u.1, by rw [hneg, u.2]⟩
      invFun := fun u => ⟨-u.1, by rw [hneg, u.2]; decide⟩
      left_inv := fun u => by simp
      right_inv := fun u => by simp }
  have hcompl : ∀ u : Integersˣ, ¬ residue u = 1 ↔ residue u = -1 := by
    intro u
    rcases residue_unit u with h | h <;> simp [h] <;> decide
  have hsum : Nat.card {u : Integersˣ // residue u = 1} +
      Nat.card {u : Integersˣ // residue u = -1} = 6 := by
    rw [← card_units, ← Nat.card_congr (Equiv.sumCompl fun u : Integersˣ => residue u = 1),
      Nat.card_sum, Nat.card_congr (Equiv.subtypeEquivRight hcompl)]
  have h1 : Nat.card {u : Integersˣ // residue u = 1} = 3 := by
    rw [Nat.card_congr e] at hsum ⊢; omega
  rcases ht with rfl | rfl
  · exact h1
  · rw [← Nat.card_congr e, h1]

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

/-- Each ideal of norm `K` with `3 ∤ K` has exactly three generators congruent to one. -/
theorem card_primarySet (K : ℕ) (hK : ¬ 3 ∣ K) :
    Nat.card (primarySet K) = 3 * idealCount K := by
  have hK0 : K ≠ 0 := fun h => hK (h ▸ dvd_zero 3)
  let e := (normSetEquiv K).trans (generatorEquiv K hK0)
  have he : ∀ p : normSet K,
      residue (gen (e p).1.1 * (e p).2) = residue (coord p.1) := by
    intro p
    change residue (gen (Ideal.span {coord p.1}) * unitOf (coord p.1)) = _
    rw [gen_mul_unitOf]
  let e₁ : primarySet K ≃ {p : normSet K // (3 : ℤ) ∣ 1 - p.1.1 - p.1.2} :=
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {p : normSet K // (3 : ℤ) ∣ 1 - p.1.1 - p.1.2} ≃
      {x : {I : Ideal Integers // Ideal.absNorm I = K} × Integersˣ //
        residue (gen x.1.1 * x.2) = 1} :=
    e.subtypeEquiv fun p => by rw [dvd_iff_residue, he]
  haveI : Finite {I : Ideal Integers // Ideal.absNorm I = K} :=
    (Ideal.finite_setOf_absNorm_eq K).to_subtype
  rw [Nat.card_congr (e₁.trans e₂), idealCount, mul_comm]
  apply WeightedCount.card_eq_mul_of_fibres (fun x => x.1.1) 3 (by norm_num)
  intro I
  have hs := residue_gen I hK
  let t := residue (gen I.1)
  have ht : t * t = 1 := by rcases hs with h | h <;> simp [t, h]
  have hfwd : ∀ x : {x : {x : {I : Ideal Integers // Ideal.absNorm I = K} × Integersˣ //
      residue (gen x.1.1 * x.2) = 1} // x.1.1 = I}, residue (x.1.1.2 : Integers) = t := by
    intro x
    have h := x.1.2
    rw [x.2, map_mul] at h
    change t * residue (x.1.1.2 : Integers) = 1 at h
    calc residue (x.1.1.2 : Integers) = t * t * residue (x.1.1.2 : Integers) := by
          rw [ht, one_mul]
      _ = t := by rw [mul_assoc, h, mul_one]
  have hbwd : ∀ u : {u : Integersˣ // residue u = t}, residue (gen I.1 * u.1) = 1 := by
    intro u
    rw [map_mul, u.2]
    exact ht
  refine (Nat.card_congr
    { toFun := fun x => ⟨x.1.1.2, hfwd x⟩
      invFun := fun u => ⟨⟨(I, u.1), hbwd u⟩, rfl⟩
      left_inv := fun x => ?_
      right_inv := fun _ => rfl }).trans (card_units_residue t hs)
  obtain ⟨⟨⟨J, v⟩, hv⟩, hJ⟩ := x
  subst hJ
  rfl

end Cubic.Counting.PrimaryNormCount
