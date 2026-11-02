import Cubic.BoxAsymptotic.AngularSpacing

/-!
# Lattice-point sums over `ℤ[ζ]`

`#{v ≠ 0 : N v ≤ R} ≪ R`, `Σ_{v ≠ 0, N v ≤ R} 1/N v ≪ 1 + log R`, and the harmonic and
`Σ 1/g²` bounds used with them.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.LatticeSums

open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.AngularSpacing
open Cubic.Counting.CenteredEllipseCount (points points_finite count_bound form)

theorem abs_le_nrm (a b : ℤ) : |a| ≤ 2 * nrm (a, b) := by
  simp only [nrm]
  have : |a| ≤ a ^ 2 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have h1 := Int.one_le_abs ha
      nlinarith [sq_abs a]
  nlinarith [sq_nonneg (2 * b - a)]

theorem nrm_swap (a b : ℤ) : nrm (b, a) = nrm (a, b) := by simp only [nrm]; ring

/-- The nonzero `v` with `N v ≤ R`. -/
def ball (R : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(2 * ⌊R⌋₊ : ℤ)) (2 * ⌊R⌋₊)) ×ˢ (Finset.Icc (-(2 * ⌊R⌋₊ : ℤ)) (2 * ⌊R⌋₊))).filter
    (fun v => v ≠ 0 ∧ (nrm v : ℝ) ≤ R)

theorem mem_ball {R : ℝ} {v : ℤ × ℤ} : v ∈ ball R ↔ v ≠ 0 ∧ (nrm v : ℝ) ≤ R := by
  rw [ball, Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨-, h⟩
  have hn : nrm v ≤ ⌊R⌋₊ := by
    have h0 := nrm_nonneg v
    have e : ((nrm v).toNat : ℝ) = nrm v := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    have : (nrm v).toNat ≤ ⌊R⌋₊ := Nat.le_floor (by rw [e]; exact h)
    omega
  obtain ⟨a, b⟩ := v
  have h1 := abs_le_nrm a b
  have h2 := abs_le_nrm b a
  rw [nrm_swap] at h2
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> [have := neg_abs_le a; have := le_abs_self a;
    have := neg_abs_le b; have := le_abs_self b] <;> simp only at * <;> omega

theorem nrm_pos_of_mem {R : ℝ} {v : ℤ × ℤ} (h : v ∈ ball R) : (1 : ℝ) ≤ nrm v := by
  exact_mod_cast one_le_nrm (mem_ball.mp h).1

theorem ball_mono {R R' : ℝ} (h : R ≤ R') : ball R ⊆ ball R' := fun v hv => by
  rw [mem_ball] at hv ⊢; exact ⟨hv.1, hv.2.trans h⟩

/-- `#{v ≠ 0 : N v ≤ R} ≤ K R`. -/
theorem card_ball : ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 0 ≤ R → ((ball R).card : ℝ) ≤ K * R := by
  obtain ⟨K₀, hK₀⟩ := count_bound
  refine ⟨2 * Real.pi / Real.sqrt 3 + |K₀| + 1, by positivity, fun R hR => ?_⟩
  rcases lt_or_ge R 1 with hR1 | hR1
  · have : ball R = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
      have := nrm_pos_of_mem hv; have := (mem_ball.mp hv).2; linarith
    rw [this, Finset.card_empty, Nat.cast_zero]; positivity
  have hinj : ((ball R).card : ℝ) ≤ Nat.card (points R) := by
    rw [Nat.card_eq_card_finite_toFinset (points_finite R)]
    exact_mod_cast Finset.card_le_card_of_injOn (fun v : ℤ × ℤ => (v.1, -v.2))
      (fun v hv => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        have := (mem_ball.mp (Finset.mem_coe.mp hv)).2
        show form (((v.1 : ℤ) : ℝ), ((-v.2 : ℤ) : ℝ)) ≤ R
        simp only [form, nrm] at this ⊢; push_cast at this ⊢; linarith)
      (fun v _ w _ h => by
        simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2)
  have h := (abs_le.mp (hK₀ R hR1)).2
  have hs : Real.sqrt R ≤ R := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have := mul_le_mul_of_nonneg_left hs (abs_nonneg K₀)
  have := le_abs_self K₀
  nlinarith [Real.sqrt_nonneg R]

/-- `Σ_{v ≠ 0, N v ≤ R} 1/N v ≤ K (1 + log R)`. -/
theorem sum_inv_ball : ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
    ∑ v ∈ ball R, (1 / (nrm v : ℝ)) ≤ K * (1 + Real.log R) := by
  obtain ⟨K, hK, hc⟩ := card_ball
  refine ⟨8 * K, by positivity, fun R hR => ?_⟩
  set j : ℤ × ℤ → ℕ := fun v => Nat.log 2 (nrm v).toNat
  set J := Nat.log 2 ⌊R⌋₊
  have hto : ∀ v ∈ ball R, ((nrm v).toNat : ℝ) = nrm v := fun v _ => by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (nrm_nonneg v)]
  have hmaps : ∀ v ∈ ball R, j v ∈ Finset.range (J + 1) := by
    intro v hv
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.log_mono_right
    apply Nat.le_floor
    rw [hto v hv]; exact (mem_ball.mp hv).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i ∈ Finset.range (J + 1),
      ∑ v ∈ (ball R).filter (fun v => j v = i), (1 / (nrm v : ℝ)) ≤ 2 * K := by
    intro i _
    have hsub : (ball R).filter (fun v => j v = i) ⊆ ball ((2 : ℝ) ^ (i + 1)) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [mem_ball]
      refine ⟨(mem_ball.mp hv.1).1, ?_⟩
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (nrm v).toNat
      rw [← hto v hv.1]
      simp only [j] at hv
      rw [hv.2] at this
      exact_mod_cast this.le
    have hterm : ∀ v ∈ (ball R).filter (fun v => j v = i), 1 / (nrm v : ℝ) ≤ 1 / 2 ^ i := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hne : (nrm v).toNat ≠ 0 := by
        have := nrm_pos_of_mem hv.1; rw [← hto v hv.1] at this
        exact_mod_cast (by positivity : ((nrm v).toNat : ℝ) ≠ 0)
      have := Nat.pow_log_le_self 2 hne
      simp only [j] at hv
      rw [hv.2] at this
      have h2 : (2 : ℝ) ^ i ≤ nrm v := by rw [← hto v hv.1]; exact_mod_cast this
      exact one_div_le_one_div_of_le (by positivity) h2
    calc ∑ v ∈ (ball R).filter (fun v => j v = i), (1 / (nrm v : ℝ))
        ≤ ((ball R).filter (fun v => j v = i)).card * (1 / 2 ^ i) := by
          rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ ((ball ((2 : ℝ) ^ (i + 1))).card : ℝ) * (1 / 2 ^ i) := by
          gcongr
      _ ≤ K * 2 ^ (i + 1) * (1 / 2 ^ i) := by
          gcongr; exact hc _ (by positivity)
      _ = 2 * K := by rw [pow_succ]; field_simp
  calc ∑ i ∈ Finset.range (J + 1), ∑ v ∈ (ball R).filter (fun v => j v = i), (1 / (nrm v : ℝ))
      ≤ ∑ i ∈ Finset.range (J + 1), 2 * K := Finset.sum_le_sum hfib
    _ = 2 * K * (J + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ 8 * K * (1 + Real.log R) := by
        have hJ : (J : ℝ) * Real.log 2 ≤ Real.log R := by
          rw [← Real.log_pow]
          have h1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa using hR)
          have := Nat.pow_log_le_self 2 (by omega : ⌊R⌋₊ ≠ 0)
          apply Real.log_le_log (by positivity)
          calc ((2 : ℝ) ^ J) = ((2 ^ J : ℕ) : ℝ) := by push_cast; rfl
            _ ≤ ⌊R⌋₊ := by exact_mod_cast this
            _ ≤ R := Nat.floor_le (by linarith)
        have hl2 := Real.log_two_gt_d9
        have hlR := Real.log_nonneg hR
        have : (J : ℝ) ≤ 2 * Real.log R := by nlinarith [Nat.cast_nonneg (α := ℝ) J]
        nlinarith

/-- `Σ_{g ≤ G} 1/g ≤ 1 + log G`. -/
theorem sum_inv_le (G : ℕ) : ∑ g ∈ Finset.Icc 1 G, (1 / (g : ℝ)) ≤ 1 + Real.log G := by
  have := harmonic_le_one_add_log G
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  simpa [one_div] using this

/-- `Σ_{g ≤ G} 1/g² ≤ 2`. -/
theorem sum_inv_sq_le (G : ℕ) : ∑ g ∈ Finset.Icc 1 G, (1 / (g : ℝ) ^ 2) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (G + 1)
  have e : Finset.Ioo 0 (G + 1) = Finset.Icc 1 G := by ext; simp; omega
  rw [e] at h
  simpa [one_div] using h

end Cubic.BoxAsymptotic.LatticeSums
