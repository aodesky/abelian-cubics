import Cubic.BoxAsymptotic.AngularLocal

/-! Unit-orbit cancellation for the nonzero angular modes in `lem:local3` and `eq:Fk`.
The factor at three is sensitive to both the sixth roots of unity and the argument
of `λ³`; the proofs retain the paper's positive Fourier convention. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularUnitSums

open Complex CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData
open Cubic.BoxAsymptotic.AngularLocal Cubic.BoxAsymptotic.EisensteinCoordinates
open Cubic.Counting.EisensteinNormCount Cubic.Counting.TraceZeroLattice

def zeta : ℂ := eis (0, 1)

theorem zeta_ne_zero : zeta ≠ 0 := eis_ne_zero (by decide)

theorem norm_zeta : ‖zeta‖ = 1 := by
  have h := norm_eis_sq (0, 1)
  norm_num [nrm] at h
  dsimp [zeta]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (eis (0, 1))]

theorem zeta_poly : zeta ^ 2 + zeta + 1 = 0 := by
  apply Complex.ext
  · simp [zeta, eis, pow_two, Complex.mul_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp [zeta, eis, pow_two, Complex.mul_im]
    ring

theorem zeta_cube : zeta ^ 3 = 1 := by
  linear_combination (zeta - 1) * zeta_poly

theorem zeta_zpow_mod (k : ℤ) : zeta ^ k = zeta ^ (k % 3) := by
  calc
    _ = zeta ^ (k % 3 + 3 * (k / 3)) := by rw [Int.emod_add_mul_ediv]
    _ = _ := by
      rw [zpow_add₀ zeta_ne_zero, zpow_mul]
      simp only [zpow_ofNat, zeta_cube, one_zpow, mul_one]

theorem zeta_sum (k : ℤ) :
    1 + zeta ^ k + (zeta ^ k) ^ 2 = if 3 ∣ k then 3 else 0 := by
  rw [zeta_zpow_mod]
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have hk : 3 ∣ k := Int.dvd_of_emod_eq_zero h
    norm_num [h, hk]
  · have hk : ¬ 3 ∣ k := by omega
    simp only [h, zpow_one, if_neg hk]
    linear_combination zeta_poly
  · have hk : ¬ 3 ∣ k := by omega
    simp only [h, zpow_ofNat, if_neg hk]
    linear_combination (zeta ^ 2 - zeta + 1) * zeta_poly

theorem eis_rot (p : ℤ × ℤ) : eis (rot p) = zeta * eis p := by
  convert eis_mulE (0, 1) p using 1
  simp [mulE, rot]

theorem rot_twice (p : ℤ × ℤ) : rot (rot p) = (-p.1 + p.2, -p.1) := by
  apply Prod.ext <;> simp only [rot] <;> ring

theorem phase_rot {n : ℕ} (hn : 0 < n) {p : ℤ × ℤ}
    (hp : p ∈ normSet ((n : ℤ) ^ 3)) (k : ℤ) :
    phase k (eis (rot p)) = zeta ^ k * phase k (eis p) := by
  rw [eis_rot, phase_mul k zeta_ne_zero (nonzero_of_norm hn hp),
    phase_eq_div k zeta_ne_zero, norm_zeta]
  simp

theorem sum_rot {n : ℕ} (hn : 0 < n) {S : Set (ℤ × ℤ)}
    (hS : S ⊆ normSet ((n : ℤ) ^ 3)) (k : ℤ) :
    angularSum k (rot '' S) = zeta ^ k * angularSum k S :=
  angularSum_image rot_injective.injOn k _ fun _ hp => phase_rot hn (hS hp) k

theorem norm_partition {N : ℤ} (hN : ¬ 3 ∣ N) :
    normSet N = slice N ∪ rot '' slice N ∪ rot '' (rot '' slice N) := by
  ext p
  constructor
  · intro hp
    have h := (exactly_one (a := p.1) (b := p.2) (by rw [hp]; exact hN)).1
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨hp, h⟩)
    · right
      refine ⟨rot (rot p), ⟨rot p, ⟨⟨rot_mem hp, h⟩, rfl⟩⟩, rot_rot_rot p⟩
    · left; right
      refine ⟨rot (rot p), ⟨rot_mem (rot_mem hp), ?_⟩, rot_rot_rot p⟩
      simpa only [rot_twice] using h.neg_right
  · rintro ((h | ⟨q, hq, rfl⟩) | ⟨q, ⟨r, hr, rfl⟩, rfl⟩)
    · exact h.1
    · exact rot_mem hq.1
    · exact rot_mem (rot_mem hr.1)

theorem partition_disjoint {N : ℤ} (hN : ¬ 3 ∣ N) :
    Disjoint (slice N) (rot '' slice N) ∧
      Disjoint (slice N ∪ rot '' slice N) (rot '' (rot '' slice N)) := by
  have hp : ∀ p ∈ normSet N, ¬ (3 ∣ p.1 ∧ 3 ∣ p.2) := by
    intro p h h3
    apply hN
    rw [← h]
    exact dvd_add (dvd_sub (dvd_pow h3.1 (by norm_num))
      (dvd_mul_of_dvd_left h3.1 p.2)) (dvd_pow h3.2 (by norm_num))
  constructor
  · apply Set.disjoint_left.mpr
    rintro p h ⟨q, hq, rfl⟩
    apply hp q hq.1
    have hd : (3 : ℤ) ∣ q.1 - q.2 := h.2
    have hb := hq.2
    exact ⟨by omega, hq.2⟩
  · apply Set.disjoint_left.mpr
    rintro p h ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    rcases h with h | ⟨v, hv, he⟩
    · apply hp r hr.1
      have hd : (3 : ℤ) ∣ -r.1 := by simpa only [rot_twice] using h.2
      exact ⟨by omega, hr.2⟩
    · have he' : v = rot r := rot_injective he
      subst v
      apply hp r hr.1
      have hd : (3 : ℤ) ∣ r.1 - r.2 := hv.2
      have hb := hr.2
      exact ⟨by omega, hr.2⟩

theorem sum_norm {M : ℕ} (hM : 0 < M) (h3 : ¬ 3 ∣ M) (k : ℤ) :
    angularSum k (normSet ((M : ℤ) ^ 3)) =
      (if 3 ∣ k then 3 else 0) * angularSum k (slice ((M : ℤ) ^ 3)) := by
  have hN : ¬ (3 : ℤ) ∣ (M : ℤ) ^ 3 := by
    intro hd
    exact h3 (by exact_mod_cast Int.prime_three.dvd_of_dvd_pow hd)
  have hf := slice_finite ((M : ℤ) ^ 3)
  have hd := partition_disjoint hN
  rw [norm_partition hN, angularSum, finsum_mem_union hd.2 (hf.union (hf.image rot))
    ((hf.image rot).image rot), finsum_mem_union hd.1 hf (hf.image rot)]
  change angularSum k (slice _) + angularSum k (rot '' slice _) +
    angularSum k (rot '' (rot '' slice _)) = _
  rw [sum_rot hM (fun _ h => h.1), sum_rot hM (by
    rintro _ ⟨p, hp, rfl⟩; exact rot_mem hp.1), sum_rot hM (fun _ h => h.1)]
  rw [← zeta_sum]
  ring

theorem sum_norm_even {M : ℕ} (hM : 0 < M) (h3 : ¬ 3 ∣ M)
    {k : ℤ} (hk : Even k) :
    angularSum k (normSet ((M : ℤ) ^ 3)) =
      (if 6 ∣ k then 6 else 0) * awayCoefficient k M := by
  rw [sum_norm hM h3 k, sum_slice hM h3 k, hk.neg_one_zpow,
    awayCoefficient, if_neg h3]
  have hd : (3 : ℤ) ∣ k ↔ 6 ∣ k := by
    obtain ⟨j, rfl⟩ := hk
    omega
  simp only [hd]
  split_ifs <;> ring

end Cubic.BoxAsymptotic.AngularUnitSums
