import Cubic.BoxAsymptotic.AngularLocalData
import Mathlib.Algebra.Ring.Parity

/-! Angular refinements of the local arithmetic at three. All finite sums here are
over the actual lattice points; no analytic estimate is assumed. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularLocal

open Complex CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.ZeroModeMass
open Cubic.Counting.EisensteinNormCount Cubic.Counting.TraceZeroLattice

theorem primary_finite (M : ℕ) : (primary M).Finite :=
  (normSet_finite _).subset fun _ h => h.1

theorem neg_norm_mem {N : ℤ} {p : ℤ × ℤ} (hp : p ∈ normSet N) :
    -p ∈ normSet N := by
  change (-p.1) ^ 2 - (-p.1) * (-p.2) + (-p.2) ^ 2 = N
  simpa only [normSet, Set.mem_setOf_eq, neg_sq, neg_mul_neg] using hp

theorem neg_admissible {n : ℕ} {p : ℤ × ℤ} (hp : p ∈ admissible n) :
    -p ∈ admissible n := by
  obtain ⟨hN, hB, s, hs, hJ⟩ := hp
  refine ⟨neg_norm_mem hN, by simpa using hB.neg_right, -s, by simpa using hs, ?_⟩
  change 2 * (-p.1) - (-p.2) ≡ 3 * (-s) * n - (-s) ^ 3 [ZMOD 27]
  convert hJ.neg using 1 <;> ring

theorem eis_neg (p : ℤ × ℤ) : eis (-p) = -eis p := by
  apply Complex.ext <;> simp [eis] <;> ring

theorem nonzero_of_norm {n : ℕ} (hn : 0 < n) {p : ℤ × ℤ}
    (hp : p ∈ normSet ((n : ℤ) ^ 3)) : eis p ≠ 0 := by
  apply eis_ne_zero
  intro h
  rw [h] at hp
  have he : (n : ℤ) ^ 3 = 0 := by simpa [normSet] using hp.symm
  have : n = 0 := by exact_mod_cast (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp he
  omega

theorem angularSum_image {S : Set (ℤ × ℤ)} {f : ℤ × ℤ → ℤ × ℤ}
    (hf : S.InjOn f) (k : ℤ) (c : ℂ)
    (hphase : ∀ p ∈ S, phase k (eis (f p)) = c * phase k (eis p)) :
    angularSum k (f '' S) = c * angularSum k S := by
  rw [angularSum, finsum_mem_image hf, angularSum, mul_finsum_mem]
  exact finsum_mem_congr rfl hphase

theorem angularSum_neg {n : ℕ} (hn : 0 < n) {S : Set (ℤ × ℤ)}
    (hS : S ⊆ normSet ((n : ℤ) ^ 3)) (k : ℤ) :
    angularSum k (Neg.neg '' S) = (-1 : ℂ) ^ k * angularSum k S := by
  apply angularSum_image neg_injective.injOn
  intro p hp
  rw [eis_neg, phase_neg k (nonzero_of_norm hn (hS hp))]

theorem coefficient_eq_sum (k : ℤ) (n : ℕ) :
    coefficient k n = (1 / 6 : ℂ) * angularSum k (admissible n) := rfl

/-- The odd modes cancel under `β ↦ -β`. The positive-norm hypothesis is essential:
`LSeries` omits `n=0`, whose single lattice point has argument zero. -/
theorem coefficient_odd {k : ℤ} (hk : Odd k) {n : ℕ} (hn : 0 < n) :
    coefficient k n = 0 := by
  have hset : Neg.neg '' admissible n = admissible n := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩; exact neg_admissible hq
    · intro hp; exact ⟨-p, neg_admissible hp, neg_neg p⟩
  have h := angularSum_neg hn (S := admissible n) (fun _ h => h.1) k
  rw [hset, neg_one_zpow_eq_ite, if_neg (Int.not_even_iff_odd.mpr hk), neg_one_mul] at h
  have hz : angularSum k (admissible n) = 0 := by linear_combination (1 / 2 : ℂ) * h
  simp [coefficient_eq_sum, hz]

/-- The two allowed signs at an unramified norm. -/
theorem slice_eq_primary_union {M : ℕ} (hM : ¬ 3 ∣ M) :
    slice ((M : ℤ) ^ 3) = primary M ∪ Neg.neg '' primary M := by
  ext p
  constructor
  · rintro ⟨hN, hB⟩
    have hA : ¬ (3 : ℤ) ∣ p.1 := by
      intro hd
      have h3 : (3 : ℤ) ∣ (M : ℤ) ^ 3 := by
        rw [← hN]
        exact dvd_add (dvd_sub (dvd_pow hd (by norm_num)) (dvd_mul_of_dvd_left hd p.2))
          (dvd_pow hB (by norm_num))
      exact hM (by exact_mod_cast Int.prime_three.dvd_of_dvd_pow h3)
    have ha : p.1 ≡ 1 [ZMOD 3] ∨ -p.1 ≡ 1 [ZMOD 3] := by
      simp only [Int.modEq_iff_dvd] at *
      omega
    rcases ha with ha | ha
    · exact Or.inl ⟨hN, ha, hB⟩
    · exact Or.inr ⟨-p, ⟨neg_norm_mem hN, ha, by simpa using hB.neg_right⟩, neg_neg p⟩
  · rintro (h | ⟨q, hq, rfl⟩)
    · exact ⟨h.1, h.2.2⟩
    · exact ⟨neg_norm_mem hq.1, by simpa using hq.2.2.neg_right⟩

theorem primary_disjoint_neg (M : ℕ) : Disjoint (primary M) (Neg.neg '' primary M) := by
  apply Set.disjoint_left.mpr
  rintro p hp ⟨q, hq, rfl⟩
  have h1 := hp.2.1.dvd
  have h2 := hq.2.1.dvd
  change (3 : ℤ) ∣ 1 - (-q.1) at h1
  change (3 : ℤ) ∣ 1 - q.1 at h2
  omega

theorem sum_slice {M : ℕ} (hM : 0 < M) (h3 : ¬ 3 ∣ M) (k : ℤ) :
    angularSum k (slice ((M : ℤ) ^ 3)) =
      (1 + (-1 : ℂ) ^ k) * angularSum k (primary M) := by
  rw [slice_eq_primary_union h3, angularSum,
    finsum_mem_union (primary_disjoint_neg M) (primary_finite M)
      ((primary_finite M).image Neg.neg)]
  change angularSum k (primary M) + angularSum k (Neg.neg '' primary M) = _
  rw [angularSum_neg hM (fun _ h => h.1)]
  ring

theorem coefficient_away {M : ℕ} (hM : 0 < M) (h3 : ¬ 3 ∣ M)
    {k : ℤ} (hk : Even k) : coefficient k M = (1 / 3 : ℂ) * awayCoefficient k M := by
  rw [coefficient_eq_sum, admissible_away_three h3, sum_slice hM h3 k,
    hk.neg_one_zpow, awayCoefficient, if_neg h3]
  ring

theorem eis_ramified (p : ℤ × ℤ) :
    eis (ramifiedMap p) = ((3 * Real.sqrt 3 : ℝ) : ℂ) * (-I) * eis p := by
  apply Complex.ext
  · simp only [ramifiedMap, eis, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    push_cast
    linear_combination -(3 * (p.2 : ℝ) / 2) *
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  · simp [ramifiedMap, eis]
    ring

theorem phase_ramified {n : ℕ} (hn : 0 < n) {p : ℤ × ℤ}
    (hp : p ∈ normSet ((n : ℤ) ^ 3)) (k : ℤ) :
    phase k (eis (ramifiedMap p)) = ramifiedPhase k * phase k (eis p) := by
  have hpos : 0 < (3 * Real.sqrt 3 : ℝ) := by positivity
  have hc : (((3 * Real.sqrt 3 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [eis_ramified, phase_mul k (mul_ne_zero hc (neg_ne_zero.mpr I_ne_zero))
      (nonzero_of_norm hn hp), phase_mul k hc (neg_ne_zero.mpr I_ne_zero),
    phase_ofReal_pos k hpos, one_mul, phase_eq_div k (neg_ne_zero.mpr I_ne_zero)]
  simp [ramifiedPhase]

theorem sum_ramified {n : ℕ} (hn : 0 < n) {S : Set (ℤ × ℤ)}
    (hS : S ⊆ normSet ((n : ℤ) ^ 3)) (k : ℤ) :
    angularSum k (ramifiedMap '' S) = ramifiedPhase k * angularSum k S :=
  angularSum_image ramifiedMap_injective.injOn k _ fun _ hp => phase_ramified hn (hS hp) k

theorem coefficient_three {M : ℕ} (hM : 0 < M) (h3 : ¬ 3 ∣ M)
    {k : ℤ} (hk : Even k) :
    coefficient k (3 * M) = (1 / 3 : ℂ) * ramifiedPhase k * awayCoefficient k M := by
  rw [coefficient_eq_sum, ← ramified_image, sum_ramified hM (fun _ h => h.1),
    sum_slice hM h3 k, hk.neg_one_zpow, awayCoefficient, if_neg h3]
  ring

end Cubic.BoxAsymptotic.AngularLocal
