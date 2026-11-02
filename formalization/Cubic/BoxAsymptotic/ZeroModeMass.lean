import Cubic.BoxAsymptotic.ZeroModeData
import Cubic.BoxAsymptotic.TraceClass
import Cubic.Counting.TraceZeroLattice
import Mathlib.Algebra.Prime.Lemmas

/-!
The total angular mass (`eq:mass`), directly from `eq:cong`.
For `3 ∤ n`, admissibility is equivalent to `3 ∣ B`. For `n = 3m`, multiplication
by `λ³ = -3 - 6ζ` identifies the admissible elements with the elements of norm `m³`
whose ζ-coefficient is divisible by 3. This proves the zero-mode part of the local
table without introducing angular Hecke characters.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroModeMass

open CubicTargets.BoxAsymptotic Cubic.Counting.EisensteinNormCount
open Cubic.Counting.TraceZeroLattice Cubic.BoxAsymptotic.ZeroModeData

theorem admissible_finite (n : ℕ) : (admissible n).Finite :=
  (normSet_finite ((n : ℤ) ^ 3)).subset fun _ h => h.1

theorem mass_eq (n : ℕ) : mass n = ((admissible n).ncard : ℝ) / 6 := by
  rw [mass, muIntegral, finsum_mem_eq_finite_toFinset_sum _ (admissible_finite n)]
  simp [Set.ncard_eq_toFinset_card (admissible n) (admissible_finite n), div_eq_mul_inv, mul_comm]

/-- Square roots of a unit modulo `27` differ only by sign. -/
theorem square_roots_mod27 {x y : ℤ} (hy : ¬ 3 ∣ y)
    (h : 27 ∣ x ^ 2 - y ^ 2) : 27 ∣ x - y ∨ 27 ∣ x + y := by
  have hp : (3 : ℤ) ^ 3 ∣ (x - y) * (x + y) := by
    convert h using 1; ring
  by_cases hl : 3 ∣ x - y
  · have hr : ¬ 3 ∣ x + y := by
      intro hr
      apply hy
      have := dvd_sub hr hl
      omega
    exact Or.inl (by simpa using Int.prime_three.pow_dvd_of_dvd_mul_right 3 hr hp)
  · exact Or.inr (by simpa using Int.prime_three.pow_dvd_of_dvd_mul_left 3 hl hp)

theorem admissible_away_three {n : ℕ} (hn : ¬ 3 ∣ n) :
    admissible n = slice ((n : ℤ) ^ 3) := by
  ext p
  refine ⟨fun h => ⟨h.1, h.2.1⟩, ?_⟩
  rintro ⟨hp, hB⟩
  have hnorm : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = (n : ℤ) ^ 3 := hp
  have hn3 : ¬ (3 : ℤ) ∣ n := by exact_mod_cast hn
  have hn1 : (n : ℤ) ≡ 1 [ZMOD 3] := by
    have key : ∀ a m : ZMod 3, m ≠ 0 → a ^ 2 = m ^ 3 → m = 1 := by decide
    have hcast : (p.2 : ZMod 3) = 0 := (dvd_three_iff _).mp hB
    have he := congrArg (fun x : ℤ => (x : ZMod 3)) hnorm
    push_cast at he
    rw [hcast] at he
    have hm : (n : ZMod 3) ≠ 0 := by
      intro h; exact hn3 ((dvd_three_iff _).mpr (by exact_mod_cast h))
    have : (n : ZMod 3) = 1 := key _ _ hm (by simpa using he)
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using this)
  obtain ⟨h, hh⟩ := hn1.dvd
  obtain ⟨c, hc⟩ := hB
  have hnform : (n : ℤ) = 1 - 3 * h := by linarith
  have hsq : 27 ∣ (2 * p.1 - p.2) ^ 2 - (3 * (n : ℤ) - 1) ^ 2 := by
    refine ⟨-4 * h ^ 3 + h ^ 2 - c ^ 2, ?_⟩
    rw [hc, hnform] at hnorm ⊢
    linear_combination 4 * hnorm
  have hunit : ¬ (3 : ℤ) ∣ 3 * (n : ℤ) - 1 := by omega
  refine ⟨hp, hc ▸ dvd_mul_right 3 c, ?_⟩
  rcases square_roots_mod27 hunit hsq with hJ | hJ
  · refine ⟨1, ?_, ?_⟩
    · simpa using hn1.symm
    · apply Int.modEq_iff_dvd.mpr
      simpa using hJ.neg_right
  · refine ⟨-1, ?_, ?_⟩
    · simpa using hn1.symm
    · apply Int.modEq_iff_dvd.mpr
      convert hJ.neg_right using 1; ring

/-- If `3 ∣ n`, the trace residue is zero and the remaining condition is `27 ∣ 2A-B`. -/
theorem admissible_three (m : ℕ) (p : ℤ × ℤ) :
    p ∈ admissible (3 * m) ↔
      p ∈ normSet ((3 * (m : ℤ)) ^ 3) ∧ 3 ∣ p.2 ∧ 27 ∣ 2 * p.1 - p.2 := by
  constructor
  · rintro ⟨hN, hB, s, hs, hJ⟩
    have hs3 : (3 : ℤ) ∣ s := by
      apply Int.prime_three.dvd_of_dvd_pow (n := 2)
      have := hs.dvd
      push_cast at this
      omega
    obtain ⟨t, rfl⟩ := hs3
    refine ⟨by simpa [normSet] using hN, hB, ?_⟩
    have := hJ.dvd
    push_cast at this
    have ht : (27 : ℤ) ∣ 3 * (3 * t) * (3 * m) - (3 * t) ^ 3 :=
      ⟨t * m - t ^ 3, by ring⟩
    omega
  · rintro ⟨hN, hB, hJ⟩
    refine ⟨by simpa [normSet] using hN, hB, 0, ?_, ?_⟩
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨m, by simp⟩
    · apply Int.modEq_iff_dvd.mpr
      simpa using hJ.neg_right

/-- Multiplication by `λ³ = -3 - 6ζ`. -/
def ramifiedMap (p : ℤ × ℤ) : ℤ × ℤ := (-3 * p.1 + 6 * p.2, -6 * p.1 + 3 * p.2)

theorem ramifiedMap_injective : Function.Injective ramifiedMap := by
  intro p q h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [ramifiedMap] at h1 h2
  exact Prod.ext (by linarith) (by linarith)

theorem ramified_image (m : ℕ) : ramifiedMap '' slice ((m : ℤ) ^ 3) = admissible (3 * m) := by
  ext p
  constructor
  · rintro ⟨q, ⟨hN, hB⟩, rfl⟩
    rw [admissible_three]
    refine ⟨?_, ⟨-2 * q.1 + q.2, by simp [ramifiedMap]; ring⟩, ?_⟩
    · change (-3 * q.1 + 6 * q.2) ^ 2 - (-3 * q.1 + 6 * q.2) *
        (-6 * q.1 + 3 * q.2) + (-6 * q.1 + 3 * q.2) ^ 2 = _
      change q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 = _ at hN
      linear_combination 27 * hN
    · obtain ⟨c, hc⟩ := hB
      exact ⟨c, by simp [ramifiedMap]; rw [hc]; ring⟩
  · intro hp
    obtain ⟨hN, hB, hJ⟩ := (admissible_three m p).mp hp
    obtain ⟨c, hc⟩ := hJ
    change p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = (3 * (m : ℤ)) ^ 3 at hN
    have h9 : (9 : ℤ) ∣ p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := ⟨3 * (m : ℤ) ^ 3, by rw [hN]; ring⟩
    obtain ⟨ha, _⟩ := three_dvd_of_nine_dvd h9
    obtain ⟨a, ha⟩ := ha
    have hBform : p.2 = 6 * a - 27 * c := by linarith
    refine ⟨(-a + 6 * c, 3 * c), ⟨?_, ⟨c, rfl⟩⟩, ?_⟩
    · change (-a + 6 * c) ^ 2 - (-a + 6 * c) * (3 * c) + (3 * c) ^ 2 = (m : ℤ) ^ 3
      rw [ha, hBform] at hN
      nlinarith [hN]
    · apply Prod.ext <;> simp only [ramifiedMap] <;> linarith

theorem ncard_ramified (m : ℕ) :
    (admissible (3 * m)).ncard = (slice ((m : ℤ) ^ 3)).ncard := by
  rw [← ramified_image, Set.ncard_image_of_injective _ ramifiedMap_injective]

open Cubic.Counting.EisensteinIdealCount Cubic.PoissonSummation

theorem norm_card (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) :
    ((normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3)).ncard : ℝ) =
      6 * (HeightCountingCoefficients.coefficient M : ℝ) := by
  have h := card_normSet ((3 ^ e * M) ^ 3) (by positivity)
  rw [Nat.card_coe_set_eq] at h
  have hI := idealCount_cube e M hM h3
  have hc : (((3 ^ e * M) ^ 3 : ℕ) : ℤ) = ((3 ^ e * M : ℕ) : ℤ) ^ 3 := by push_cast; rfl
  rw [hc] at h
  have hr : ((normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3)).ncard : ℝ) =
      6 * (idealCount ((3 ^ e * M) ^ 3) : ℝ) := by exact_mod_cast h
  have hIr : (idealCount ((3 ^ e * M) ^ 3) : ℝ) =
      (HeightCountingCoefficients.coefficient M : ℝ) := by exact_mod_cast hI
  rw [hr, hIr]

theorem slice_card (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) :
    ((slice (((3 ^ e * M : ℕ) : ℤ) ^ 3)).ncard : ℝ) =
      (if e = 0 then 2 else 6) * (HeightCountingCoefficients.coefficient M : ℝ) := by
  rcases e.eq_zero_or_pos with rfl | he
  · have h3' : ¬ (3 : ℤ) ∣ (M : ℤ) ^ 3 := by
      intro h; exact h3 (by exact_mod_cast Int.prime_three.dvd_of_dvd_pow h)
    have h := three_mul_ncard_slice h3'
    have hn := norm_card 0 M hM h3
    simp only [pow_zero, one_mul, ↓reduceIte] at hn ⊢
    have h' : (3 : ℝ) * (slice ((M : ℤ) ^ 3)).ncard = (normSet ((M : ℤ) ^ 3)).ncard := by
      exact_mod_cast h
    linarith
  · have h9 : (9 : ℤ) ∣ ((3 ^ e * M : ℕ) : ℤ) ^ 3 := by
      have hd : (3 : ℤ) ∣ ((3 ^ e * M : ℕ) : ℤ) := by
        exact_mod_cast (dvd_mul_of_dvd_left (dvd_pow_self 3 he.ne') M)
      obtain ⟨k, hk⟩ := hd
      exact ⟨3 * k ^ 3, by rw [hk]; ring⟩
    rw [slice_eq_of_nine_dvd h9, if_neg he.ne']
    exact norm_card e M hM h3

/-- The exact local mass table `eq:mass`, with `d_M` expressed by its proved arithmetic
coefficient formula. No angular equidistribution or Poisson input is used here. -/
theorem «eq:mass» (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) :
    mass (3 ^ e * M) =
      (if e < 2 then (1 / 3 : ℝ) else 1) * HeightCountingCoefficients.coefficient M := by
  rw [mass_eq]
  rcases e with _ | e
  · rw [pow_zero, one_mul, admissible_away_three h3]
    have h := slice_card 0 M hM h3
    simp only [pow_zero, one_mul, ↓reduceIte] at h
    rw [h]; norm_num; ring
  · have hm : 3 ^ (e + 1) * M = 3 * (3 ^ e * M) := by ring
    rw [hm, ncard_ramified, slice_card e M hM h3]
    rcases e with _ | e
    · norm_num; ring
    · simp

end Cubic.BoxAsymptotic.ZeroModeMass
