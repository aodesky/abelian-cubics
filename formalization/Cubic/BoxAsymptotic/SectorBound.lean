import Cubic.BoxAsymptotic.LatticeSums

/-!
# `lem:sector`: the sector upper bound

For `X ≥ 2` and `Θ ≥ 0`, the number of `β ∈ ℤ[ζ]` with `N β = n³` for some
`X ≤ n ≤ 2X` and `arg β` within `Θ` of `θ₀` modulo `2π` is `≪ (ΘX + √X) log X`.

Proof as in the draft. Write `β = u · N(γ)γ · g³δ₀³` (`EisensteinCoordinates.decomposition`),
so `n = N(γ) g² N(δ₀)` and `arg β ≡ arg u + arg γ + 3 arg δ₀`. If `N γ ≤ N δ₀`, fix
`(u, γ, g)`: then `arg δ₀` lies in one of three arcs of half-width `Θ/3`, and `N δ₀ ≤ T`
with `T = 2X/(N(γ) g²)`, so angular spacing (`AngularSpacing.card_le`) allows at most
`8ΘX/(√3 N(γ) g²) + 3` values, and none unless `N(γ)² g² ≤ 2X`. If `N δ₀ < N γ`, fix
`(u, δ₀, g)` and argue in the same way with `γ`. Summing over the fixed variables
(`outer`), with `Σ 1/N v ≪ log X`, `Σ 1/g² ≤ 2` and `Σ_g √X/g ≪ √X log X`, gives the
bound. (The draft's dyadic decomposition in `N γ ≍ U`, `N δ ≍ V` is replaced by this split,
which gives the same sums.)
-/

noncomputable section

namespace Cubic.BoxAsymptotic.SectorBound

open CubicTargets.BoxAsymptotic (eis)
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.AngularSpacing
open Cubic.BoxAsymptotic.LatticeSums
open Real

/-- `arg β ≡ arg u + arg γ + 3 arg δ₀ (mod 2π)` for `β = u · N(γ)γ · g³δ₀³`. -/
theorem arg_assemble {u γ δ₀ : ℤ × ℤ} {g : ℕ} (hu : u ≠ 0) (hγ : γ ≠ 0) (hδ : δ₀ ≠ 0)
    (hg : 0 < g) : ∃ m : ℤ, Complex.arg (eis (assemble u γ δ₀ g)) =
      Complex.arg (eis u) + Complex.arg (eis γ) + 3 * Complex.arg (eis δ₀) + 2 * π * m := by
  have hr : 0 < (nrm γ : ℝ) * (g : ℝ) ^ 3 := by
    have := one_le_nrm hγ
    have : (1 : ℝ) ≤ nrm γ := by exact_mod_cast this
    positivity
  have hu' := eis_ne_zero hu
  have hγ' := eis_ne_zero hγ
  have hδ' := eis_ne_zero hδ
  have e : eis (assemble u γ δ₀ g) =
      (((nrm γ : ℝ) * (g : ℝ) ^ 3 : ℝ) : ℂ) * (eis u * (eis γ * eis δ₀ ^ 3)) := by
    rw [eis_assemble]; ring
  have ha : (Complex.arg (eis (assemble u γ δ₀ g)) : Real.Angle) =
      ((Complex.arg (eis u) + Complex.arg (eis γ) + 3 * Complex.arg (eis δ₀) : ℝ) : Real.Angle) := by
    rw [e, Complex.arg_real_mul _ hr,
      Complex.arg_mul_coe_angle hu' (mul_ne_zero hγ' (pow_ne_zero 3 hδ')),
      Complex.arg_mul_coe_angle hγ' (pow_ne_zero 3 hδ'), Complex.arg_pow_coe_angle,
      Real.Angle.coe_add, Real.Angle.coe_add, ← Real.Angle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    abel
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp ha
  exact ⟨m, by linarith⟩

theorem log_facts {X : ℝ} (hX : 2 ≤ X) :
    1 ≤ 2 * Real.log X ∧ Real.log (Real.sqrt (2 * X)) ≤ Real.log X := by
  have hl2 := Real.log_two_gt_d9
  have h1 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  refine ⟨by linarith, ?_⟩
  rw [Real.log_sqrt (by linarith), Real.log_mul (by norm_num) (by linarith)]
  linarith

/-- The sum over the fixed variables. -/
theorem outer : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 2 ≤ X → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    ∑ v ∈ ball (Real.sqrt (2 * X)), ∑ g ∈ Finset.Icc 1 ⌊Real.sqrt (2 * X)⌋₊,
        (a * X / ((nrm v : ℝ) * (g : ℝ) ^ 2) +
          if (nrm v : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then b else 0) ≤
      K * (a * X + b * Real.sqrt X) * Real.log X := by
  obtain ⟨K₀, hK₀, hc⟩ := card_ball
  obtain ⟨K₁, hK₁, hs⟩ := sum_inv_ball
  refine ⟨6 * (K₀ + K₁), by positivity, fun X hX a b ha hb => ?_⟩
  obtain ⟨hl1, hl2⟩ := log_facts hX
  have hX0 : 0 < X := by linarith
  set R := Real.sqrt (2 * X) with hR
  set G := ⌊R⌋₊
  have hR1 : 1 ≤ R := by rw [hR, Real.le_sqrt' (by norm_num)]; linarith
  have hRX : R ≤ 2 * Real.sqrt X := by
    rw [hR, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have hG1 : 1 ≤ G := Nat.le_floor (by simpa using hR1)
  have hlogG : Real.log G ≤ Real.log X :=
    (Real.log_le_log (by exact_mod_cast hG1) (Nat.floor_le (by linarith))).trans hl2
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the main part
  have hmain : ∑ v ∈ ball R, ∑ g ∈ Finset.Icc 1 G, a * X / ((nrm v : ℝ) * (g : ℝ) ^ 2) ≤
      6 * K₁ * a * X * Real.log X := by
    calc ∑ v ∈ ball R, ∑ g ∈ Finset.Icc 1 G, a * X / ((nrm v : ℝ) * (g : ℝ) ^ 2)
        = ∑ v ∈ ball R, (a * X * (1 / (nrm v : ℝ))) *
            ∑ g ∈ Finset.Icc 1 G, (1 / (g : ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          field_simp
      _ ≤ ∑ v ∈ ball R, (a * X * (1 / (nrm v : ℝ))) * 2 := by
          refine Finset.sum_le_sum fun v hv => ?_
          have := nrm_pos_of_mem hv
          exact mul_le_mul_of_nonneg_left (sum_inv_sq_le G) (by positivity)
      _ = 2 * a * X * ∑ v ∈ ball R, (1 / (nrm v : ℝ)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ 2 * a * X * (K₁ * (1 + Real.log R)) :=
          mul_le_mul_of_nonneg_left (hs R hR1) (by positivity)
      _ ≤ 6 * K₁ * a * X * Real.log X := by
          have : 2 * a * X * K₁ * (1 + Real.log R) ≤ 2 * a * X * K₁ * (3 * Real.log X) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith
  -- the `+1` part
  have hcount : ∀ g ∈ Finset.Icc 1 G,
      ((ball R).filter (fun v => (nrm v : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X)).card ≤
        K₀ * (R / g) := by
    intro g hg
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
    refine le_trans ?_ (hc (R / g) (by positivity))
    refine Nat.cast_le.mpr (Finset.card_le_card fun v hv => ?_)
    rw [Finset.mem_filter] at hv
    rw [mem_ball] at hv ⊢
    refine ⟨hv.1.1, ?_⟩
    have hn1 : (1 : ℝ) ≤ nrm v := by exact_mod_cast one_le_nrm hv.1.1
    rw [le_div_iff₀ (by linarith), hR, Real.le_sqrt (by nlinarith) (by linarith)]
    nlinarith [hv.2]
  have hplus : ∑ v ∈ ball R, ∑ g ∈ Finset.Icc 1 G,
      (if (nrm v : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then b else 0) ≤
        6 * K₀ * b * Real.sqrt X * Real.log X := by
    rw [Finset.sum_comm]
    calc ∑ g ∈ Finset.Icc 1 G, ∑ v ∈ ball R,
          (if (nrm v : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then b else 0)
        = ∑ g ∈ Finset.Icc 1 G,
            b * ((ball R).filter (fun v => (nrm v : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X)).card := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ g ∈ Finset.Icc 1 G, b * (K₀ * (R / g)) :=
          Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (hcount g hg) hb
      _ = b * K₀ * R * ∑ g ∈ Finset.Icc 1 G, (1 / (g : ℝ)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ b * K₀ * R * (1 + Real.log G) :=
          mul_le_mul_of_nonneg_left (sum_inv_le G) (by positivity)
      _ ≤ b * K₀ * (2 * Real.sqrt X) * (3 * Real.log X) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRX (by positivity)) (by linarith)
            (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ G by exact_mod_cast hG1)])
            (by positivity)
      _ = 6 * K₀ * b * Real.sqrt X * Real.log X := by ring
  have hlog0 : 0 ≤ Real.log X := by linarith
  have e1 : 6 * K₁ * a * X * Real.log X ≤ 6 * (K₀ + K₁) * (a * X) * Real.log X := by
    have : 0 ≤ 6 * K₀ * (a * X) * Real.log X := by positivity
    nlinarith
  have e2 : 6 * K₀ * b * Real.sqrt X * Real.log X ≤
      6 * (K₀ + K₁) * (b * Real.sqrt X) * Real.log X := by
    have : 0 ≤ 6 * K₁ * (b * Real.sqrt X) * Real.log X := by positivity
    nlinarith
  nlinarith


/-- The count for fixed `(u, γ, g)` when `N γ ≤ N δ₀`. -/
theorem innerA {X θ₀ Θ : ℝ} (hX : 0 < X) (hΘ : 0 ≤ Θ) {u γ : ℤ × ℤ} {g : ℕ} (hu : u ≠ 0)
    (hγ : γ ≠ 0) (hg : 1 ≤ g) (W : Finset (ℤ × ℤ)) [DecidablePred fun δ₀ : ℤ × ℤ =>
      prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
        near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm γ ≤ nrm δ₀] :
    ((W.filter fun δ₀ => prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
        near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm γ ≤ nrm δ₀).card : ℝ) ≤
      8 * Θ / Real.sqrt 3 * X / ((nrm γ : ℝ) * (g : ℝ) ^ 2) +
        if (nrm γ : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then 3 else 0 := by
  set F := W.filter fun δ₀ => prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
    near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm γ ≤ nrm δ₀
  have hc1 : (1 : ℝ) ≤ nrm γ := by exact_mod_cast one_le_nrm hγ
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hpos : 0 < (nrm γ : ℝ) * (g : ℝ) ^ 2 := by positivity
  have hmain : 0 ≤ 8 * Θ / Real.sqrt 3 * X / ((nrm γ : ℝ) * (g : ℝ) ^ 2) := by positivity
  split_ifs with hcase
  · set T := 2 * X / ((nrm γ : ℝ) * (g : ℝ) ^ 2)
    set a : ℕ → ℝ := fun j =>
      (θ₀ - Complex.arg (eis u) - Complex.arg (eis γ) + 2 * π * j) / 3
    classical
    have hsub : F ⊆ (Finset.range 3).biUnion fun j =>
        F.filter fun δ₀ => near (Complex.arg (eis δ₀)) (a j) (Θ / 3) := by
      intro δ₀ hδ
      have hδ' := (Finset.mem_filter.mp hδ).2
      obtain ⟨k, hk⟩ := hδ'.2.2.2.1
      obtain ⟨m, hm⟩ := arg_assemble hu hγ (prim_ne_zero hδ'.2.1) (by omega : 0 < g)
      rw [Finset.mem_biUnion]
      refine ⟨((k - m) % 3).toNat, ?_, Finset.mem_filter.mpr ⟨hδ, (k - m) / 3, ?_⟩⟩
      · rw [Finset.mem_range]; omega
      · have e : (((k - m) % 3).toNat : ℝ) = ((k - m) % 3 : ℤ) := by
          have : 0 ≤ (k - m) % 3 := Int.emod_nonneg _ (by norm_num)
          exact_mod_cast Int.toNat_of_nonneg this
        have e2 : ((k - m : ℤ) : ℝ) = ((k - m) % 3 : ℤ) + 3 * ((k - m) / 3 : ℤ) := by
          exact_mod_cast (Int.emod_add_mul_ediv (k - m) 3).symm
        simp only [a]
        rw [e]
        push_cast at e2
        rw [hm] at hk
        rw [show Complex.arg (eis δ₀) - (θ₀ - Complex.arg (eis u) - Complex.arg (eis γ) +
            2 * π * (((k - m) % 3 : ℤ) : ℝ)) / 3 - 2 * π * (((k - m) / 3 : ℤ) : ℝ) =
            (Complex.arg (eis u) + Complex.arg (eis γ) + 3 * Complex.arg (eis δ₀) +
              2 * π * m - θ₀ - 2 * π * k) / 3 by
          have : (k : ℝ) = m + ((k - m) % 3 : ℤ) + 3 * ((k - m) / 3 : ℤ) := by linarith
          rw [this]; ring]
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        exact div_le_div_of_nonneg_right hk (by norm_num)
    have hj : ∀ j ∈ Finset.range 3,
        (((F.filter fun δ₀ => near (Complex.arg (eis δ₀)) (a j) (Θ / 3)).card : ℕ) : ℝ) ≤
          4 * (Θ / 3) * T / Real.sqrt 3 + 1 := by
      intro j _
      refine card_le (a := a j) (by positivity) (by positivity) fun δ₀ hδ => ?_
      rw [Finset.mem_filter] at hδ
      have hδ' := (Finset.mem_filter.mp hδ.1).2
      refine ⟨hδ'.2.1, ?_, hδ.2⟩
      rw [le_div_iff₀ hpos]; linarith [hδ'.2.2.1]
    calc (F.card : ℝ) ≤ (((Finset.range 3).biUnion fun j =>
          F.filter fun δ₀ => near (Complex.arg (eis δ₀)) (a j) (Θ / 3)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.range 3,
          (((F.filter fun δ₀ => near (Complex.arg (eis δ₀)) (a j) (Θ / 3)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range 3, (4 * (Θ / 3) * T / Real.sqrt 3 + 1) := Finset.sum_le_sum hj
      _ = 8 * Θ / Real.sqrt 3 * X / ((nrm γ : ℝ) * (g : ℝ) ^ 2) + 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp only [T]; field_simp; ring
  · have : F = ∅ := Finset.eq_empty_of_forall_notMem fun δ₀ hδ => by
      have hδ' := (Finset.mem_filter.mp hδ).2
      have h1 : (nrm γ : ℝ) ≤ nrm δ₀ := by exact_mod_cast hδ'.2.2.2.2
      apply hcase
      have := hδ'.2.2.1
      nlinarith
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]; exact hmain

/-- The count for fixed `(u, δ₀, g)` when `N δ₀ < N γ`. -/
theorem innerB {X θ₀ Θ : ℝ} (hX : 0 < X) (hΘ : 0 ≤ Θ) {u δ₀ : ℤ × ℤ} {g : ℕ} (hu : u ≠ 0)
    (hδ : δ₀ ≠ 0) (hg : 1 ≤ g) (W : Finset (ℤ × ℤ)) [DecidablePred fun γ : ℤ × ℤ =>
      prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
        near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm δ₀ < nrm γ] :
    ((W.filter fun γ => prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
        near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm δ₀ < nrm γ).card : ℝ) ≤
      8 * Θ / Real.sqrt 3 * X / ((nrm δ₀ : ℝ) * (g : ℝ) ^ 2) +
        if (nrm δ₀ : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then 1 else 0 := by
  set F := W.filter fun γ => prim γ ∧ prim δ₀ ∧ (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ ≤ 2 * X ∧
    near (Complex.arg (eis (assemble u γ δ₀ g))) θ₀ Θ ∧ nrm δ₀ < nrm γ
  have hc1 : (1 : ℝ) ≤ nrm δ₀ := by exact_mod_cast one_le_nrm hδ
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hpos : 0 < (nrm δ₀ : ℝ) * (g : ℝ) ^ 2 := by positivity
  have hmain : 0 ≤ 8 * Θ / Real.sqrt 3 * X / ((nrm δ₀ : ℝ) * (g : ℝ) ^ 2) := by positivity
  split_ifs with hcase
  · set T := 2 * X / ((nrm δ₀ : ℝ) * (g : ℝ) ^ 2)
    have := card_le (S := F) (T := T)
      (a := θ₀ - Complex.arg (eis u) - 3 * Complex.arg (eis δ₀)) (ℓ := Θ)
      (by positivity) hΘ fun γ hγ => by
        have hγ' := (Finset.mem_filter.mp hγ).2
        refine ⟨hγ'.1, ?_, ?_⟩
        · rw [le_div_iff₀ hpos]; linarith [hγ'.2.2.1]
        · obtain ⟨k, hk⟩ := hγ'.2.2.2.1
          obtain ⟨m, hm⟩ := arg_assemble hu (prim_ne_zero hγ'.1) hδ (by omega : 0 < g)
          refine ⟨k - m, ?_⟩
          rw [hm] at hk
          push_cast
          convert hk using 2; ring
    calc (F.card : ℝ) ≤ 4 * Θ * T / Real.sqrt 3 + 1 := this
      _ = 8 * Θ / Real.sqrt 3 * X / ((nrm δ₀ : ℝ) * (g : ℝ) ^ 2) + 1 := by
          simp only [T]; field_simp; ring
  · have : F = ∅ := Finset.eq_empty_of_forall_notMem fun γ hγ => by
      have hγ' := (Finset.mem_filter.mp hγ).2
      have h1 : (nrm δ₀ : ℝ) < nrm γ := by exact_mod_cast hγ'.2.2.2.2
      apply hcase
      have := hγ'.2.2.1
      nlinarith
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]; exact hmain


theorem prod_facts {c G m P : ℝ} (hc : 1 ≤ c) (hG : 1 ≤ G) (hm : 1 ≤ m) (hP : c * G * m ≤ P) :
    G ≤ P ∧ c ≤ P ∧ m ≤ P ∧ (c ≤ m → c ^ 2 ≤ P) ∧ (m ≤ c → m ^ 2 ≤ P) := by
  have h1 : 0 ≤ G * (c * m - 1) := mul_nonneg (by linarith) (by nlinarith)
  have h2 : 0 ≤ c * (G * m - 1) := mul_nonneg (by linarith) (by nlinarith)
  have h3 : 0 ≤ m * (c * G - 1) := mul_nonneg (by linarith) (by nlinarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, fun h => ?_, fun h => ?_⟩
  · have : 0 ≤ c * (m - c) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ c * m * (G - 1) := mul_nonneg (by nlinarith) (by linarith)
    nlinarith
  · have : 0 ≤ m * (c - m) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ c * m * (G - 1) := mul_nonneg (by nlinarith) (by linarith)
    nlinarith

theorem card_filter_product {α β : Type*} (s : Finset α) (t : Finset β) (p : α × β → Prop)
    [DecidablePred p] :
    ((s ×ˢ t).filter p).card = ∑ a ∈ s, (t.filter fun b => p (a, b)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

/-- **`lem:sector`.** For `X ≥ 2` and `Θ ≥ 0`, any finite set of `β` with `N β = n³` for some
`X ≤ n ≤ 2X` and `arg β` within `Θ` of `θ₀` modulo `2π` has at most
`K (ΘX + √X) log X` elements. -/
theorem «lem:sector» : ∃ K : ℝ, 0 < K ∧ ∀ X θ₀ Θ : ℝ, 2 ≤ X → 0 ≤ Θ →
    ∀ S : Finset (ℤ × ℤ), (∀ β ∈ S, (∃ n : ℕ, X ≤ n ∧ (n : ℝ) ≤ 2 * X ∧ nrm β = (n : ℤ) ^ 3) ∧
      near (Complex.arg (eis β)) θ₀ Θ) →
    (S.card : ℝ) ≤ K * (Θ * X + Real.sqrt X) * Real.log X := by
  obtain ⟨Ko, hKo, hout⟩ := outer
  set U := ball 1
  refine ⟨22 * (U.card + 1) * Ko, by positivity, fun X θ₀ Θ hX hΘ S hS => ?_⟩
  classical
  have hX0 : 0 < X := by linarith
  -- decompose every `β`
  have hdec : ∀ β ∈ S, ∃ t : (ℤ × ℤ) × (ℤ × ℤ) × ℕ × (ℤ × ℤ),
      nrm t.1 = 1 ∧ prim t.2.1 ∧ prim t.2.2.2 ∧ 1 ≤ t.2.2.1 ∧
      (nrm t.2.1 : ℝ) * (t.2.2.1 : ℝ) ^ 2 * nrm t.2.2.2 ≤ 2 * X ∧
      β = assemble t.1 t.2.1 t.2.2.2 t.2.2.1 := by
    intro β hβ
    obtain ⟨n, hn1, hn2, hn⟩ := (hS β hβ).1
    have hn0 : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
    obtain ⟨u, γ, δ₀, g, hu, hγ, hδ, hg, he, hb⟩ := decomposition hn0 hn
    refine ⟨(u, γ, g, δ₀), hu, hγ, hδ, hg, ?_, hb⟩
    have : (n : ℝ) = (nrm γ : ℝ) * (g : ℝ) ^ 2 * nrm δ₀ := by exact_mod_cast he
    simp only; linarith
  choose! t ht using hdec
  set R := Real.sqrt (2 * X) with hR
  set Gs := Finset.Icc 1 ⌊R⌋₊
  set W := ball (2 * X)
  set V := ball R
  -- common facts
  have hfacts : ∀ β ∈ S, (t β).1 ∈ U ∧ (t β).2.2.1 ∈ Gs ∧ (t β).2.1 ∈ W ∧ (t β).2.2.2 ∈ W ∧
      near (Complex.arg (eis (assemble (t β).1 (t β).2.1 (t β).2.2.2 (t β).2.2.1))) θ₀ Θ ∧
      ((nrm (t β).2.1 ≤ nrm (t β).2.2.2 → (t β).2.1 ∈ V) ∧
        (nrm (t β).2.2.2 < nrm (t β).2.1 → (t β).2.2.2 ∈ V)) := by
    intro β hβ
    obtain ⟨hu, hγ, hδ, hg, hP, hb⟩ := ht β hβ
    have hγ1 : (1 : ℝ) ≤ nrm (t β).2.1 := by exact_mod_cast one_le_nrm (prim_ne_zero hγ)
    have hδ1 : (1 : ℝ) ≤ nrm (t β).2.2.2 := by exact_mod_cast one_le_nrm (prim_ne_zero hδ)
    have hg1 : (1 : ℝ) ≤ (t β).2.2.1 := by exact_mod_cast hg
    have hg2 : (1 : ℝ) ≤ ((t β).2.2.1 : ℝ) ^ 2 := by nlinarith
    obtain ⟨p1, p2, p3, p4, p5⟩ := prod_facts hγ1 hg2 hδ1 hP
    refine ⟨mem_ball.mpr ⟨fun h => by rw [h] at hu; simp [nrm] at hu, by rw [hu]; norm_num⟩,
      Finset.mem_Icc.mpr ⟨hg, Nat.le_floor ?_⟩, mem_ball.mpr ⟨prim_ne_zero hγ, ?_⟩,
      mem_ball.mpr ⟨prim_ne_zero hδ, ?_⟩, hb ▸ (hS β hβ).2, fun h => mem_ball.mpr
        ⟨prim_ne_zero hγ, ?_⟩, fun h => mem_ball.mpr ⟨prim_ne_zero hδ, ?_⟩⟩
    · rw [hR, Real.le_sqrt (by positivity) (by linarith)]; exact p1
    · exact p2
    · exact p3
    · have h' : (nrm (t β).2.1 : ℝ) ≤ nrm (t β).2.2.2 := by exact_mod_cast h
      rw [hR, Real.le_sqrt (by linarith) (by linarith)]; exact p4 h'
    · have h' : (nrm (t β).2.2.2 : ℝ) < nrm (t β).2.1 := by exact_mod_cast h
      rw [hR, Real.le_sqrt (by linarith) (by linarith)]; exact p5 h'.le
  -- region A: `N γ ≤ N δ₀`
  set PA : (ℤ × ℤ) × (ℤ × ℤ) × ℕ × (ℤ × ℤ) → Prop := fun x =>
    prim x.2.1 ∧ prim x.2.2.2 ∧ (nrm x.2.1 : ℝ) * (x.2.2.1 : ℝ) ^ 2 * nrm x.2.2.2 ≤ 2 * X ∧
      near (Complex.arg (eis (assemble x.1 x.2.1 x.2.2.2 x.2.2.1))) θ₀ Θ ∧
      nrm x.2.1 ≤ nrm x.2.2.2
  set SA := S.filter fun β => nrm (t β).2.1 ≤ nrm (t β).2.2.2
  have hA : (SA.card : ℝ) ≤ U.card * (Ko * (8 * Θ / Real.sqrt 3 * X + 3 * Real.sqrt X) *
      Real.log X) := by
    have hinj : SA.card ≤ ((U ×ˢ (V ×ˢ (Gs ×ˢ W))).filter PA).card := by
      refine Finset.card_le_card_of_injOn t (fun β hβ => ?_) (fun β hβ β' hβ' h => ?_)
      · rw [Finset.mem_coe, Finset.mem_filter] at hβ
        obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hfacts β hβ.1
        obtain ⟨-, hγ, hδ, -, hP, -⟩ := ht β hβ.1
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
          Finset.mem_product]
        exact ⟨⟨h1, h6 hβ.2, h2, h4⟩, hγ, hδ, hP, h5, hβ.2⟩
      · rw [Finset.mem_coe, Finset.mem_filter] at hβ hβ'
        rw [(ht β hβ.1).2.2.2.2.2, (ht β' hβ'.1).2.2.2.2.2, h]
    calc (SA.card : ℝ) ≤ ((U ×ˢ (V ×ˢ (Gs ×ˢ W))).filter PA).card := by exact_mod_cast hinj
      _ = ∑ u ∈ U, ∑ γ ∈ V, ∑ g ∈ Gs,
          ((W.filter fun δ₀ => PA (u, γ, g, δ₀)).card : ℝ) := by
          rw [card_filter_product]; push_cast
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [card_filter_product]; push_cast
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [card_filter_product]; push_cast; rfl
      _ ≤ ∑ u ∈ U, ∑ γ ∈ V, ∑ g ∈ Gs,
          (8 * Θ / Real.sqrt 3 * X / ((nrm γ : ℝ) * (g : ℝ) ^ 2) +
            if (nrm γ : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then 3 else 0) := by
          refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun γ hγ =>
            Finset.sum_le_sum fun g hg => ?_
          have hu0 : u ≠ 0 := (mem_ball.mp hu).1
          exact innerA hX0 hΘ hu0 (mem_ball.mp hγ).1 (Finset.mem_Icc.mp hg).1 W
      _ ≤ ∑ u ∈ U, Ko * (8 * Θ / Real.sqrt 3 * X + 3 * Real.sqrt X) * Real.log X :=
          Finset.sum_le_sum fun u _ => hout X hX _ 3 (by positivity) (by norm_num)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- region B: `N δ₀ < N γ`
  set PB : (ℤ × ℤ) × (ℤ × ℤ) × ℕ × (ℤ × ℤ) → Prop := fun x =>
    prim x.2.2.2 ∧ prim x.2.1 ∧ (nrm x.2.2.2 : ℝ) * (x.2.2.1 : ℝ) ^ 2 * nrm x.2.1 ≤ 2 * X ∧
      near (Complex.arg (eis (assemble x.1 x.2.2.2 x.2.1 x.2.2.1))) θ₀ Θ ∧
      nrm x.2.1 < nrm x.2.2.2
  set SB := S.filter fun β => ¬ nrm (t β).2.1 ≤ nrm (t β).2.2.2
  set tB : ℤ × ℤ → (ℤ × ℤ) × (ℤ × ℤ) × ℕ × (ℤ × ℤ) := fun β =>
    ((t β).1, (t β).2.2.2, (t β).2.2.1, (t β).2.1)
  have hB : (SB.card : ℝ) ≤ U.card * (Ko * (8 * Θ / Real.sqrt 3 * X + 1 * Real.sqrt X) *
      Real.log X) := by
    have hinj : SB.card ≤ ((U ×ˢ (V ×ˢ (Gs ×ˢ W))).filter PB).card := by
      refine Finset.card_le_card_of_injOn tB (fun β hβ => ?_) (fun β hβ β' hβ' h => ?_)
      · rw [Finset.mem_coe, Finset.mem_filter] at hβ
        obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hfacts β hβ.1
        obtain ⟨-, hγ, hδ, -, hP, -⟩ := ht β hβ.1
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
          Finset.mem_product]
        exact ⟨⟨h1, h7 (not_le.mp hβ.2), h2, h3⟩, hγ, hδ, hP, h5, not_le.mp hβ.2⟩
      · rw [Finset.mem_coe, Finset.mem_filter] at hβ hβ'
        simp only [tB, Prod.mk.injEq] at h
        rw [(ht β hβ.1).2.2.2.2.2, (ht β' hβ'.1).2.2.2.2.2, h.1, h.2.1, h.2.2.1, h.2.2.2]
    calc (SB.card : ℝ) ≤ ((U ×ˢ (V ×ˢ (Gs ×ˢ W))).filter PB).card := by exact_mod_cast hinj
      _ = ∑ u ∈ U, ∑ δ₀ ∈ V, ∑ g ∈ Gs,
          ((W.filter fun γ => PB (u, δ₀, g, γ)).card : ℝ) := by
          rw [card_filter_product]; push_cast
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [card_filter_product]; push_cast
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [card_filter_product]; push_cast; rfl
      _ ≤ ∑ u ∈ U, ∑ δ₀ ∈ V, ∑ g ∈ Gs,
          (8 * Θ / Real.sqrt 3 * X / ((nrm δ₀ : ℝ) * (g : ℝ) ^ 2) +
            if (nrm δ₀ : ℝ) ^ 2 * (g : ℝ) ^ 2 ≤ 2 * X then 1 else 0) := by
          refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun δ₀ hδ =>
            Finset.sum_le_sum fun g hg => ?_
          have hu0 : u ≠ 0 := (mem_ball.mp hu).1
          exact innerB hX0 hΘ hu0 (mem_ball.mp hδ).1 (Finset.mem_Icc.mp hg).1 W
      _ ≤ ∑ u ∈ U, Ko * (8 * Θ / Real.sqrt 3 * X + 1 * Real.sqrt X) * Real.log X :=
          Finset.sum_le_sum fun u _ => hout X hX _ 1 (by positivity) (by norm_num)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- total
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun β => nrm (t β).2.1 ≤ nrm (t β).2.2.2)
  have hS' : (S.card : ℝ) = SA.card + SB.card := by rw [← hsplit]; push_cast; ring
  have h3 : 1 ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h8 : 8 * Θ / Real.sqrt 3 ≤ 8 * Θ := div_le_self (by positivity) h3
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsq := Real.sqrt_nonneg X
  have hUc : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have key : Ko * (8 * Θ / Real.sqrt 3 * X + 3 * Real.sqrt X) * Real.log X +
      Ko * (8 * Θ / Real.sqrt 3 * X + 1 * Real.sqrt X) * Real.log X ≤
        22 * Ko * (Θ * X + Real.sqrt X) * Real.log X := by
    have : 8 * Θ / Real.sqrt 3 * X ≤ 8 * Θ * X := mul_le_mul_of_nonneg_right h8 hX0.le
    have hΘX : 0 ≤ Θ * X := by positivity
    have : (8 * Θ / Real.sqrt 3 * X + 3 * Real.sqrt X) + (8 * Θ / Real.sqrt 3 * X + 1 * Real.sqrt X)
        ≤ 22 * (Θ * X + Real.sqrt X) := by nlinarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hKo.le hlog)
    nlinarith
  have hfin : (U.card : ℝ) * (22 * Ko * (Θ * X + Real.sqrt X) * Real.log X) ≤
      22 * (U.card + 1) * Ko * (Θ * X + Real.sqrt X) * Real.log X := by
    have : 0 ≤ 22 * Ko * (Θ * X + Real.sqrt X) * Real.log X := by positivity
    nlinarith
  rw [hS']
  nlinarith [mul_le_mul_of_nonneg_left key hUc]

end Cubic.BoxAsymptotic.SectorBound
