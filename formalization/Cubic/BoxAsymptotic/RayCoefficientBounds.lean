import Cubic.BoxAsymptotic.PrimitiveRays

/-! The coefficient-square estimate in the angular large sieve. It is proved
for arbitrary subsets of a norm ball, so it can be applied to norm intervals
without imposing regularity or multiplicativity on their coefficients. -/

noncomputable section

namespace Cubic.BoxAsymptotic.RayCoefficientBounds

open Cubic.BoxAsymptotic.PrimitiveRays Cubic.BoxAsymptotic.LatticeSums
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.AngularSpacing

def rays (Y : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (ball Y).filter prim

def onRay (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  S.filter (fun p => primitivePart p = v)

def mass (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (v : ℤ × ℤ) : ℝ :=
  ∑ p ∈ onRay S v, ‖c p‖

theorem mass_nonneg (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (v : ℤ × ℤ) :
    0 ≤ mass S c v := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem maps_to_rays {Y : ℝ} {S : Finset (ℤ × ℤ)} (hS : S ⊆ ball Y)
    {p : ℤ × ℤ} (hp : p ∈ S) : primitivePart p ∈ rays Y := by
  classical
  exact Finset.mem_filter.mpr ⟨primitivePart_mem (hS hp), primitive (mem_ball.mp (hS hp)).1⟩

theorem harmonic_floor {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ g ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (g : ℝ))) ≤ 1 + Real.log Y := by
  have hfloor : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
  have hpos : (0 : ℝ) < ⌊Y⌋₊ := by exact_mod_cast (by omega : 0 < ⌊Y⌋₊)
  have hlog := Real.log_le_log hpos (Nat.floor_le (by linarith : 0 ≤ Y))
  linarith [sum_inv_le ⌊Y⌋₊]

theorem ray_mass_bound {Y : ℝ} (hY : 1 ≤ Y) {S : Finset (ℤ × ℤ)}
    (hS : S ⊆ ball Y) (c : ℤ × ℤ → ℂ)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ 1 / Real.sqrt (nrm p))
    (v : ℤ × ℤ) : mass S c v ≤ (1 + Real.log Y) / Real.sqrt (nrm v) := by
  classical
  have hcontent : ∀ p ∈ onRay S v, content p ∈ Finset.Icc 1 ⌊Y⌋₊ := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    refine Finset.mem_Icc.mpr ⟨content_pos (mem_ball.mp (hS hpS)).1, ?_⟩
    exact Nat.le_floor (content_le (hS hpS))
  have hi : Set.InjOn content (onRay S v) := by
    intro p hp q hq he
    exact content_injective_on_ray v (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2 he
  have hsum : (∑ p ∈ onRay S v, 1 / (content p : ℝ)) ≤
      ∑ g ∈ Finset.Icc 1 ⌊Y⌋₊, 1 / (g : ℝ) := by
    rw [← Finset.sum_image (f := fun g : ℕ => (1 : ℝ) / g) hi]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro g hg
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
      exact hcontent p hp
    · intro g _ _
      positivity
  calc
    mass S c v ≤ ∑ p ∈ onRay S v,
        (1 / (content p : ℝ)) * (1 / Real.sqrt (nrm v)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpS, hpv⟩ := Finset.mem_filter.mp hp
      calc
        ‖c p‖ ≤ 1 / Real.sqrt (nrm p) := hc p hpS
        _ = _ := by rw [sqrt_norm_decompose p, hpv, one_div_mul_one_div]
    _ = (∑ p ∈ onRay S v, 1 / (content p : ℝ)) / Real.sqrt (nrm v) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (1 + Real.log Y) / Real.sqrt (nrm v) :=
      div_le_div_of_nonneg_right (hsum.trans (harmonic_floor hY)) (Real.sqrt_nonneg _)

theorem energy_bound : ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 1 ≤ Y →
    ∀ (S : Finset (ℤ × ℤ)), S ⊆ ball Y → ∀ (c : ℤ × ℤ → ℂ),
      (∀ p ∈ S, ‖c p‖ ≤ 1 / Real.sqrt (nrm p)) →
      (∑ v ∈ rays Y, mass S c v ^ 2) ≤ C * (1 + Real.log Y) ^ 3 := by
  obtain ⟨C, hC, hsum⟩ := sum_inv_ball
  classical
  refine ⟨C, hC, fun Y hY S hS c hc => ?_⟩
  have hterm : ∀ v ∈ rays Y, mass S c v ^ 2 ≤
      (1 + Real.log Y) ^ 2 * (1 / (nrm v : ℝ)) := by
    intro v hv
    have hn : (0 : ℝ) ≤ nrm v := by exact_mod_cast nrm_nonneg v
    have h := pow_le_pow_left₀ (mass_nonneg S c v) (ray_mass_bound hY hS c hc v) 2
    rw [div_pow, Real.sq_sqrt hn] at h
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hsubset : rays Y ⊆ ball Y := Finset.filter_subset _ _
  have hinv : (∑ v ∈ rays Y, 1 / (nrm v : ℝ)) ≤ C * (1 + Real.log Y) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_) (hsum Y hY)
    intro v _ _
    exact one_div_nonneg.mpr (by exact_mod_cast nrm_nonneg v)
  calc
    (∑ v ∈ rays Y, mass S c v ^ 2) ≤
        ∑ v ∈ rays Y, (1 + Real.log Y) ^ 2 * (1 / (nrm v : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (1 + Real.log Y) ^ 2 * ∑ v ∈ rays Y, 1 / (nrm v : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (1 + Real.log Y) ^ 2 * (C * (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = C * (1 + Real.log Y) ^ 3 := by ring

end Cubic.BoxAsymptotic.RayCoefficientBounds
