import Cubic.BoxAsymptotic.Admissible

/-!
# Dyadic bands of admissible `β` and the sector bound

`lem:sector` for the admissible pairs `(n, β)`: `n` is determined by `β`, so a set of
pairs with `X ≤ n ≤ 2X` and `arg β` within `Θ` of `θ₀` has at most `K (ΘX + √X) log X`
elements. Also: `1 - cos φ ≥ 2φ²/π²` on `[-π, π]`, so `1 - |cos θ| ≤ δ` puts `θ` within
`π √(δ/2)` of `0` or `π`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Bands

open CubicTargets.BoxAsymptotic (eis admissible)
open Cubic.BoxAsymptotic.EisensteinCoordinates (nrm)
open Cubic.BoxAsymptotic.AngularSpacing (near)
open Cubic.BoxAsymptotic.Admissible
open Real

theorem n_unique {n m : ℕ} {β : ℤ × ℤ} (hn : β ∈ admissible n) (hm : β ∈ admissible m) :
    n = m := by
  have h1 : nrm β = (n : ℤ) ^ 3 := hn.1
  have h2 : nrm β = (m : ℤ) ^ 3 := hm.1
  have : (n : ℤ) ^ 3 = (m : ℤ) ^ 3 := h1.symm.trans h2
  exact_mod_cast (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp this

/-- `lem:sector` for admissible pairs. -/
theorem sector : ∃ K : ℝ, 0 < K ∧ ∀ (H X θ₀ Θ : ℝ), 2 ≤ X → 0 ≤ Θ →
    ∀ F : Finset (ℕ × (ℤ × ℤ)), F ⊆ Bset H →
      (∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ near (θ x.2) θ₀ Θ) →
      (F.card : ℝ) ≤ K * (Θ * X + Real.sqrt X) * Real.log X := by
  obtain ⟨K, hK, hs⟩ := Cubic.BoxAsymptotic.SectorBound.«lem:sector»
  refine ⟨K, hK, fun H X θ₀ Θ hX hΘ F hF hmem => ?_⟩
  classical
  have hinj : Set.InjOn Prod.snd (F : Set (ℕ × (ℤ × ℤ))) := by
    intro x hx y hy h
    have hx' := (mem_Bset.mp (by simpa using hF hx : (x.1, x.2) ∈ Bset H)).2.2
    have hy' := (mem_Bset.mp (by simpa using hF hy : (y.1, y.2) ∈ Bset H)).2.2
    rw [h] at hx'
    exact Prod.ext (n_unique hx' hy') h
  rw [← Finset.card_image_of_injOn hinj]
  refine hs X θ₀ Θ hX hΘ _ fun β hβ => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨h1, h2, h3⟩ := hmem x hx
  have hadm := (mem_Bset.mp (by simpa using hF hx : (x.1, x.2) ∈ Bset H)).2.2
  exact ⟨⟨x.1, h1, h2, hadm.1⟩, h3⟩

/-- `1 - cos φ ≥ 2φ²/π²` for `|φ| ≤ π`. -/
theorem one_sub_cos_ge {φ : ℝ} (h : |φ| ≤ π) : 2 * φ ^ 2 / π ^ 2 ≤ 1 - Real.cos φ := by
  have hc : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at this
    have h2 := Real.sin_sq_add_cos_sq (φ / 2)
    linarith
  rw [hc]
  have ha : 0 ≤ |φ| / 2 := by positivity
  have hb : |φ| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin ha hb
  have hsin : |Real.sin (φ / 2)| = Real.sin (|φ| / 2) := by
    rcases le_total 0 φ with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [abs_of_nonneg h0] at h; linarith))]
    · rw [abs_of_nonpos h0] at h ⊢
      have hn : 0 ≤ Real.sin (-φ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith)
      rw [show -φ / 2 = -(φ / 2) by ring, Real.sin_neg] at hn ⊢
      rw [abs_of_nonpos (by linarith)]
  have hsq : (2 / π * (|φ| / 2)) ^ 2 ≤ Real.sin (φ / 2) ^ 2 := by
    rw [← sq_abs (Real.sin _), hsin]
    exact pow_le_pow_left₀ (by positivity) hs 2
  have hpi : 0 < π := Real.pi_pos
  have : (2 / π * (|φ| / 2)) ^ 2 = φ ^ 2 / π ^ 2 := by
    rw [show 2 / π * (|φ| / 2) = |φ| / π by field_simp, div_pow, sq_abs]
  rw [this] at hsq
  have e : 2 * φ ^ 2 / π ^ 2 = 2 * (φ ^ 2 / π ^ 2) := by ring
  rw [e]
  linarith

/-- If `1 - cos φ ≤ δ` then `φ` is within `π√(δ/2)` of `0` modulo `2π`. -/
theorem near_zero_of_cos {φ δ : ℝ} (h : 1 - Real.cos φ ≤ δ) :
    near φ 0 (π * Real.sqrt (δ / 2)) := by
  set t := toIocMod Real.two_pi_pos (-π) φ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, φ - t = k • (2 * π) :=
    ⟨toIocDiv Real.two_pi_pos (-π) φ, by
      rw [show t = toIocMod Real.two_pi_pos (-π) φ from rfl, toIocMod]; ring⟩
  have ht := toIocMod_mem_Ioc Real.two_pi_pos (-π) φ
  have htπ : |t| ≤ π := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcos : Real.cos t = Real.cos φ := by
    rw [show φ = t + (k : ℝ) * (2 * π) by rw [zsmul_eq_mul] at hk; linarith,
      Real.cos_add_int_mul_two_pi]
  have hge := one_sub_cos_ge htπ
  rw [hcos] at hge
  refine ⟨k, ?_⟩
  rw [show φ - 0 - 2 * π * (k : ℝ) = t by rw [zsmul_eq_mul] at hk; linarith]
  have hpi : 0 < π := Real.pi_pos
  have hδ : 0 ≤ δ := by
    have : 0 ≤ 2 * t ^ 2 / π ^ 2 := by positivity
    linarith
  have : t ^ 2 ≤ (π * Real.sqrt (δ / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hge
    nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.mpr h

/-- If `1 - |cos θ| ≤ δ`, then `θ` is within `π√(δ/2)` of `0` or of `π`. -/
theorem near_of_cos {θ δ : ℝ} (h : 1 - |Real.cos θ| ≤ δ) :
    near θ 0 (π * Real.sqrt (δ / 2)) ∨ near θ π (π * Real.sqrt (δ / 2)) := by
  rcases le_total 0 (Real.cos θ) with h0 | h0
  · left; rw [abs_of_nonneg h0] at h; exact near_zero_of_cos h
  · right
    rw [abs_of_nonpos h0] at h
    have : 1 - Real.cos (θ - π) ≤ δ := by rw [Real.cos_sub_pi]; linarith
    obtain ⟨k, hk⟩ := near_zero_of_cos this
    exact ⟨k, by convert hk using 2; ring⟩


theorem near_mono {θ θ₀ Θ Θ' : ℝ} (h : near θ θ₀ Θ) (hΘ : Θ ≤ Θ') : near θ θ₀ Θ' := by
  obtain ⟨k, hk⟩ := h; exact ⟨k, hk.trans hΘ⟩

/-- Every angle is within `π` of any `θ₀`. -/
theorem near_pi (θ θ₀ : ℝ) : near θ θ₀ π := by
  set t := toIocMod Real.two_pi_pos (-π) (θ - θ₀)
  have ht := toIocMod_mem_Ioc Real.two_pi_pos (-π) (θ - θ₀)
  refine ⟨toIocDiv Real.two_pi_pos (-π) (θ - θ₀), ?_⟩
  have e : θ - θ₀ - 2 * π * (toIocDiv Real.two_pi_pos (-π) (θ - θ₀) : ℝ) = t := by
    rw [show t = toIocMod Real.two_pi_pos (-π) (θ - θ₀) from rfl, toIocMod, zsmul_eq_mul]; ring
  rw [e, abs_le]; constructor <;> linarith [ht.1, ht.2]

/-- The dyadic index `⌊log₂ n⌋`. -/
def band (x : ℕ × (ℤ × ℤ)) : ℕ := Nat.log 2 x.1

theorem band_bounds {x : ℕ × (ℤ × ℤ)} (hx : 1 ≤ x.1) :
    (2 : ℝ) ^ band x ≤ x.1 ∧ (x.1 : ℝ) < 2 ^ (band x + 1) := by
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  · exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) x.1

theorem Nmax_le {H : ℝ} (hH : 3 ≤ H) : (Nmax H : ℝ) ≤ 2 * H ^ 2 :=
  (Nat.floor_le (by positivity)).trans (by nlinarith)

theorem mem_bands {H : ℝ} {x : ℕ × (ℤ × ℤ)} (hx : x ∈ Bset H) :
    band x ∈ Finset.range (Nat.log 2 (Nmax H) + 1) := by
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.log_mono_right (mem_Bset.mp (by simpa using hx)).2.1

/-- `log X ≤ 3 log H` for `1 ≤ X ≤ 2H²`, `H ≥ 3`. -/
theorem log_le {H X : ℝ} (hH : 3 ≤ H) (hX : 1 ≤ X) (hXH : X ≤ 2 * H ^ 2) :
    Real.log X ≤ 3 * Real.log H := by
  have h1 : Real.log X ≤ Real.log (2 * H ^ 2) := Real.log_le_log (by linarith) hXH
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) (by linarith)
  push_cast at h1; linarith

/-- The number of bands is at most `6 log H` for `H ≥ 3`. -/
theorem card_bands {H : ℝ} (hH : 3 ≤ H) :
    ((Nat.log 2 (Nmax H) + 1 : ℕ) : ℝ) ≤ 6 * Real.log H := by
  have hN := Nmax_le hH
  have hN1 : 1 ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
  have hp := Nat.pow_log_le_self 2 (by omega : Nmax H ≠ 0)
  have hl : ((Nat.log 2 (Nmax H) : ℕ) : ℝ) * Real.log 2 ≤ Real.log (Nmax H) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hp)
  have hlN := log_le hH (by exact_mod_cast hN1) hN
  have hl2 := Real.log_two_gt_d9
  have hlH : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
  have hl3 : 1 < Real.log 3 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    have h3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]; exact h3
  push_cast
  have : ((Nat.log 2 (Nmax H) : ℕ) : ℝ) ≤ 5 * Real.log H := by
    have : ((Nat.log 2 (Nmax H) : ℕ) : ℝ) * Real.log 2 ≤ 3 * Real.log H := hl.trans hlN
    nlinarith
  linarith


open Cubic.BoxAsymptotic.TraceWidth (E W W_le_sqrt angle_of_nonempty)
open scoped Classical

theorem sqrt_pow' {a : ℝ} (ha : 0 ≤ a) (i : ℕ) : Real.sqrt (a ^ i) = Real.sqrt a ^ i := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) i), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

/-- The pairs with `n = 1` are at most a constant. -/
theorem card_band_zero : ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, ∀ F ⊆ Bset H, (∀ x ∈ F, band x = 0) →
    (F.card : ℝ) ≤ K := by
  obtain ⟨K₀, hK₀, hc⟩ := Cubic.BoxAsymptotic.LatticeSums.card_ball
  refine ⟨K₀ * 1, by positivity, fun H F hF hb => ?_⟩
  classical
  have hinj : Set.InjOn Prod.snd (F : Set (ℕ × (ℤ × ℤ))) := by
    intro x hx y hy h
    have hx' := (mem_Bset.mp (by simpa using hF hx : (x.1, x.2) ∈ Bset H)).2.2
    have hy' := (mem_Bset.mp (by simpa using hF hy : (y.1, y.2) ∈ Bset H)).2.2
    rw [h] at hx'
    exact Prod.ext (n_unique hx' hy') h
  refine le_trans ?_ (hc 1 zero_le_one)
  rw [← Finset.card_image_of_injOn hinj]
  refine Nat.cast_le.mpr (Finset.card_le_card fun β hβ => ?_)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨h1, -, hadm⟩ := mem_Bset.mp (by simpa using hF hx : (x.1, x.2) ∈ Bset H)
  have hn : x.1 = 1 := by
    have := (band_bounds h1).2; rw [hb x hx] at this; norm_num at this
    have : x.1 < 2 := by exact_mod_cast this
    omega
  have hN : nrm x.2 = 1 := by
    have := hadm.1; rw [hn] at this; simpa [nrm] using this
  rw [Cubic.BoxAsymptotic.LatticeSums.mem_ball]
  refine ⟨fun h0 => by rw [h0] at hN; simp [nrm] at hN, by rw [hN]; norm_num⟩


/-- A nonempty trace set with `n ≥ X ≥ H` forces `1 - |cos θ| ≤ 54 H²/X²`. -/
theorem cos_of_nonempty {H X n θ : ℝ} (hH : 3 ≤ H) (hXH : H ≤ X) (hXn : X ≤ n)
    (hnH : n ≤ 2 * H ^ 2) (hE : (E H n θ).Nonempty) :
    1 - |Real.cos θ| ≤ 54 * H ^ 2 / X ^ 2 := by
  have hn : 0 < n := by linarith
  have h := angle_of_nonempty hn hE
  set r := Real.sqrt n
  set c := 1 - |Real.cos θ|
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn.le
  have hr2H : r ≤ 2 * H := by
    have : r ^ 2 ≤ (2 * H) ^ 2 := by rw [hr2]; nlinarith
    exact (pow_le_pow_iff_left₀ hr.le (by linarith) (by norm_num)).mp this
  have hc0 : 0 ≤ c := by simp only [c]; linarith [abs_cos_le_one θ]
  have h' : 2 * r ^ 6 * c ≤ 27 * H * r ^ 3 + 27 * H ^ 2 * r ^ 2 + 27 * H ^ 3 := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ r ^ 3)
    have e : r ^ 3 * (27 * H + 27 * H ^ 2 / r + 27 * H ^ 3 / r ^ 3) =
        27 * H * r ^ 3 + 27 * H ^ 2 * r ^ 2 + 27 * H ^ 3 := by field_simp
    nlinarith
  have t1 : 27 * H * r ^ 3 ≤ 54 * H ^ 2 * r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hr2H (by positivity : (0 : ℝ) ≤ 27 * H * r ^ 2)
    nlinarith
  have t2 : 27 * H ^ 3 ≤ 27 * H ^ 2 * r ^ 2 := by
    have : H ≤ r ^ 2 := by rw [hr2]; linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 27 * H ^ 2)
    nlinarith
  have h4 : r ^ 4 * c ≤ 54 * H ^ 2 := by
    have : r ^ 2 * (r ^ 4 * c) ≤ r ^ 2 * (54 * H ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hX4 : X ^ 2 ≤ r ^ 4 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
    exact pow_le_pow_left₀ (by linarith) hXn 2
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- `π √27 ≤ 17`. -/
theorem pi_sqrt27 : π * Real.sqrt 27 ≤ 17 := by
  have h1 : Real.sqrt 27 ≤ 5.2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 := Real.pi_lt_d2
  nlinarith [Real.sqrt_nonneg 27, Real.pi_pos]

/-- **The `β` with a nonempty trace set**: at most `K H (log H)²`. -/
theorem card_nonempty : ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 3 ≤ H →
    (((Bset H).filter fun x : ℕ × (ℤ × ℤ) => (E H x.1 (θ x.2)).Nonempty).card : ℝ) ≤
      K * H * Real.log H ^ 2 := by
  obtain ⟨Ks, hKs, hsec⟩ := sector
  obtain ⟨K₀, hK₀, h0⟩ := card_band_zero
  refine ⟨6 * (K₀ + 114 * Ks), by positivity, fun H hH => ?_⟩
  classical
  set F := (Bset H).filter fun x : ℕ × (ℤ × ℤ) => (E H x.1 (θ x.2)).Nonempty
  set I := Nat.log 2 (Nmax H)
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hmaps : ∀ x ∈ F, band x ∈ Finset.range (I + 1) := fun x hx =>
    mem_bands (Finset.mem_filter.mp hx).1
  rw [Finset.card_eq_sum_card_fiberwise (f := band) (t := Finset.range (I + 1)) (fun x hx => Finset.mem_coe.mpr (hmaps x hx))]
  have hband : ∀ i ∈ Finset.range (I + 1),
      (((F.filter fun x => band x = i)).card : ℝ) ≤ (K₀ + 114 * Ks) * H * Real.log H := by
    intro i _
    set Fi := F.filter fun x => band x = i
    have hFi : Fi ⊆ Bset H := fun x hx =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have := h0 H Fi hFi fun x hx => (Finset.mem_filter.mp hx).2
      have : K₀ ≤ K₀ * H * Real.log H := by
        have : 1 ≤ H * Real.log H := by nlinarith
        nlinarith
      nlinarith
    set X : ℝ := 2 ^ i
    have hX2 : 2 ≤ X := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
      simpa [X] using this
    have hmem : ∀ x ∈ Fi, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ (x.1 : ℝ) ≤ 2 * H ^ 2 ∧
        (E H x.1 (θ x.2)).Nonempty := by
      intro x hx
      have hxF := (Finset.mem_filter.mp hx)
      have hxB := (Finset.mem_filter.mp hxF.1)
      obtain ⟨h1, hN, -⟩ := mem_Bset.mp (by simpa using hxB.1 : (x.1, x.2) ∈ Bset H)
      have hb := band_bounds h1
      rw [hxF.2] at hb
      refine ⟨hb.1, by rw [pow_succ] at hb; linarith [hb.2], ?_, hxB.2⟩
      exact (by exact_mod_cast hN : (x.1 : ℝ) ≤ Nmax H).trans (Nmax_le hH)
    rcases Fi.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he, Finset.card_empty, Nat.cast_zero]
      have : 0 ≤ Real.log H := by linarith
      positivity
    have hXH2 : X ≤ 2 * H ^ 2 := (hmem x₀ hx₀).1.trans (hmem x₀ hx₀).2.2.1
    set Θ : ℝ := if H ≤ X then 17 * H / X else π
    have hΘ0 : 0 ≤ Θ := by
      simp only [Θ]; split_ifs
      · positivity
      · exact Real.pi_pos.le
    have hΘX : Θ * X ≤ 17 * H := by
      simp only [Θ]; split_ifs with h
      · rw [div_mul_cancel₀ _ (by positivity)]
      · have := Real.pi_lt_d2; nlinarith
    have hnear : ∀ x ∈ Fi, near (θ x.2) 0 Θ ∨ near (θ x.2) π Θ := by
      intro x hx
      obtain ⟨h1, -, h3, h4⟩ := hmem x hx
      by_cases hHX : H ≤ X
      · have hc := cos_of_nonempty hH hHX h1 h3 h4
        have hΘ' : π * Real.sqrt (54 * H ^ 2 / X ^ 2 / 2) ≤ Θ := by
          simp only [Θ, if_pos hHX]
          rw [show 54 * H ^ 2 / X ^ 2 / 2 = 27 * (H / X) ^ 2 by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
          have := pi_sqrt27
          have hHX0 : 0 ≤ H / X := by positivity
          calc π * (Real.sqrt 27 * (H / X)) = (π * Real.sqrt 27) * (H / X) := by ring
            _ ≤ 17 * (H / X) := mul_le_mul_of_nonneg_right this hHX0
            _ = 17 * H / X := by ring
        rcases near_of_cos hc with h | h
        · exact Or.inl (near_mono h hΘ')
        · exact Or.inr (near_mono h hΘ')
      · simp only [Θ, if_neg hHX]; exact Or.inl (near_pi _ _)
    have hsplit : Fi ⊆ (Fi.filter fun x => near (θ x.2) 0 Θ) ∪
        (Fi.filter fun x => near (θ x.2) π Θ) := by
      intro x hx
      rcases hnear x hx with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
    have hsec' : ∀ θ₀, (((Fi.filter fun x => near (θ x.2) θ₀ Θ)).card : ℝ) ≤
        Ks * (Θ * X + Real.sqrt X) * Real.log X := fun θ₀ =>
      hsec H X θ₀ Θ hX2 hΘ0 _ (fun x hx => hFi (Finset.mem_filter.mp hx).1)
        fun x hx => ⟨(hmem x (Finset.mem_filter.mp hx).1).1,
          (hmem x (Finset.mem_filter.mp hx).1).2.1, (Finset.mem_filter.mp hx).2⟩
    have hsq : Real.sqrt X ≤ 2 * H := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlog := log_le hH (by linarith) hXH2
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hone : Ks * (Θ * X + Real.sqrt X) * Real.log X ≤ Ks * (19 * H) * (3 * Real.log H) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hKs.le) hlog hlog0
      positivity
    calc ((Fi.card : ℕ) : ℝ) ≤ (((Fi.filter fun x => near (θ x.2) 0 Θ) ∪
          (Fi.filter fun x => near (θ x.2) π Θ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsplit
      _ ≤ (((Fi.filter fun x => near (θ x.2) 0 Θ)).card : ℝ) +
          (((Fi.filter fun x => near (θ x.2) π Θ)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ 2 * (Ks * (19 * H) * (3 * Real.log H)) := by linarith [hsec' 0, hsec' π, hone]
      _ ≤ (K₀ + 114 * Ks) * H * Real.log H := by
          have := mul_nonneg (mul_nonneg hK₀.le (by linarith : (0 : ℝ) ≤ H))
            (by linarith : (0 : ℝ) ≤ Real.log H)
          linarith
  push_cast
  calc ∑ i ∈ Finset.range (I + 1), (((F.filter fun x => band x = i)).card : ℝ)
      ≤ ∑ _i ∈ Finset.range (I + 1), (K₀ + 114 * Ks) * H * Real.log H := Finset.sum_le_sum hband
    _ = ((I + 1 : ℕ) : ℝ) * ((K₀ + 114 * Ks) * H * Real.log H) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (6 * Real.log H) * ((K₀ + 114 * Ks) * H * Real.log H) :=
        mul_le_mul_of_nonneg_right (card_bands hH)
          (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
    _ = 6 * (K₀ + 114 * Ks) * H * Real.log H ^ 2 := by ring


/-- `β = A` real has argument `0` or `π`. -/
theorem near_of_real {β : ℤ × ℤ} (hB : β.2 = 0) : near (θ β) 0 0 ∨ near (θ β) π 0 := by
  have he : eis β = ((β.1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [eis, hB]
  rcases le_or_gt 0 β.1 with h | h
  · left; refine ⟨0, ?_⟩
    rw [θ, he, Complex.arg_ofReal_of_nonneg (by exact_mod_cast h)]; simp
  · right; refine ⟨0, ?_⟩
    rw [θ, he, Complex.arg_ofReal_of_neg (by exact_mod_cast h)]; simp

/-- `q = 2^{1/4} > 1.18`. -/
theorem q_gt : (1.18 : ℝ) < Real.sqrt (Real.sqrt 2) := by
  rw [Real.lt_sqrt (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num

/-- `Σ_{i ≤ I} qⁱ ≤ q^{I+1}/(q - 1)`. -/
theorem geom_le {q : ℝ} (hq : 1 < q) (I : ℕ) :
    ∑ i ∈ Finset.range (I + 1), q ^ i ≤ q ^ (I + 1) / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq), div_le_div_iff_of_pos_right (by linarith)]
  linarith

/-- **The real `β` (`B = 0`)**: `Σ W ≤ K H log H`. -/
theorem sum_real : ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 3 ≤ H →
    ∑ x ∈ (Bset H).filter (fun x : ℕ × (ℤ × ℤ) => x.2.2 = 0), W H x.1 (θ x.2) ≤
      K * H * Real.log H := by
  obtain ⟨Ks, hKs, hsec⟩ := sector
  obtain ⟨K₀, hK₀, h0⟩ := card_band_zero
  set q := Real.sqrt (Real.sqrt 2)
  have hq := q_gt
  refine ⟨4 * K₀ * Real.sqrt 54 + 48 * Ks * Real.sqrt 54 * (Real.sqrt 2 / (q - 1)),
    by have : 0 < q - 1 := by linarith
       positivity, fun H hH => ?_⟩
  set F := (Bset H).filter (fun x : ℕ × (ℤ × ℤ) => x.2.2 = 0)
  set I := Nat.log 2 (Nmax H)
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hmaps : ∀ x ∈ F, band x ∈ Finset.range (I + 1) := fun x hx =>
    mem_bands (Finset.mem_filter.mp hx).1
  rw [← Finset.sum_fiberwise_of_maps_to (g := band) (t := Finset.range (I + 1))
    (fun x hx => hmaps x hx)]
  have hW : ∀ x ∈ F, W H x.1 (θ x.2) ≤ 4 * Real.sqrt (54 * H / Real.sqrt x.1) := by
    intro x hx
    have h1 := (mem_Bset.mp (by simpa using (Finset.mem_filter.mp hx).1 :
      (x.1, x.2) ∈ Bset H)).1
    exact W_le_sqrt (by exact_mod_cast h1)
  have hW0 : ∀ x : ℕ × (ℤ × ℤ), 0 ≤ W H x.1 (θ x.2) := fun x =>
    Cubic.BoxAsymptotic.TraceWidth.W_nonneg _ _ _
  have hsqH : Real.sqrt 54 * Real.sqrt H ≤ Real.sqrt 54 * H := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  -- band `i`
  have hband : ∀ i ∈ Finset.range (I + 1),
      ∑ x ∈ F.filter (fun x => band x = i), W H x.1 (θ x.2) ≤
        (if i = 0 then 4 * K₀ * (Real.sqrt 54 * Real.sqrt H) else 0) +
          24 * Ks * Real.log H * (Real.sqrt 54 * Real.sqrt H) * q ^ i := by
    intro i _
    set Fi := F.filter fun x => band x = i
    have hFi : Fi ⊆ Bset H := fun x hx =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hq0 : 0 ≤ 24 * Ks * Real.log H * (Real.sqrt 54 * Real.sqrt H) * q ^ i := by
      have : 0 ≤ Real.log H := by linarith
      positivity
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [if_pos rfl]
      have hc := h0 H Fi hFi fun x hx => (Finset.mem_filter.mp hx).2
      have hWi : ∀ x ∈ Fi, W H x.1 (θ x.2) ≤ 4 * (Real.sqrt 54 * Real.sqrt H) := by
        intro x hx
        have hx1 : x.1 = 1 := by
          have h1 := (mem_Bset.mp (by simpa using hFi hx : (x.1, x.2) ∈ Bset H)).1
          have := (band_bounds h1).2; rw [(Finset.mem_filter.mp hx).2] at this
          norm_num at this
          have : x.1 < 2 := by exact_mod_cast this
          omega
        have := hW x (Finset.mem_filter.mp hx).1
        rw [hx1] at this ⊢; simpa [Real.sqrt_mul' _ (show (0 : ℝ) ≤ H by linarith)] using this
      calc ∑ x ∈ Fi, W H x.1 (θ x.2) ≤ ∑ _x ∈ Fi, 4 * (Real.sqrt 54 * Real.sqrt H) :=
            Finset.sum_le_sum hWi
        _ = Fi.card * (4 * (Real.sqrt 54 * Real.sqrt H)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ K₀ * (4 * (Real.sqrt 54 * Real.sqrt H)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ ≤ _ := by nlinarith
    · rw [if_neg (by omega), zero_add]
      set X : ℝ := 2 ^ i
      have hX2 : 2 ≤ X := by
        have : (2 : ℝ) ^ 1 ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
        simpa [X] using this
      have hmem : ∀ x ∈ Fi, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ (x.1 : ℝ) ≤ 2 * H ^ 2 := by
        intro x hx
        obtain ⟨h1, hN, -⟩ := mem_Bset.mp (by simpa using hFi hx : (x.1, x.2) ∈ Bset H)
        have hb := band_bounds h1
        rw [(Finset.mem_filter.mp hx).2] at hb
        exact ⟨hb.1, by rw [pow_succ] at hb; linarith [hb.2],
          (by exact_mod_cast hN : (x.1 : ℝ) ≤ Nmax H).trans (Nmax_le hH)⟩
      rcases Fi.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
      · rw [he, Finset.sum_empty]; exact hq0
      have hXH2 : X ≤ 2 * H ^ 2 := (hmem x₀ hx₀).1.trans (hmem x₀ hx₀).2.2
      have hsplit : Fi ⊆ (Fi.filter fun x => near (θ x.2) 0 0) ∪
          (Fi.filter fun x => near (θ x.2) π 0) := by
        intro x hx
        have hB : x.2.2 = 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
        rcases near_of_real hB with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      have hsec' : ∀ θ₀, (((Fi.filter fun x => near (θ x.2) θ₀ 0)).card : ℝ) ≤
          Ks * (0 * X + Real.sqrt X) * Real.log X := fun θ₀ =>
        hsec H X θ₀ 0 hX2 le_rfl _ (fun x hx => hFi (Finset.mem_filter.mp hx).1)
          fun x hx => ⟨(hmem x (Finset.mem_filter.mp hx).1).1,
            (hmem x (Finset.mem_filter.mp hx).1).2.1, (Finset.mem_filter.mp hx).2⟩
      have hlog := log_le hH (by linarith) hXH2
      have hcard : (Fi.card : ℝ) ≤ 2 * Ks * Real.sqrt X * (3 * Real.log H) := by
        have a := Finset.card_le_card hsplit
        have b := Finset.card_union_le (Fi.filter fun x => near (θ x.2) 0 0)
          (Fi.filter fun x => near (θ x.2) π 0)
        have c1 := hsec' 0
        have c2 := hsec' π
        have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
        have : Ks * (0 * X + Real.sqrt X) * Real.log X ≤ Ks * Real.sqrt X * (3 * Real.log H) := by
          rw [zero_mul, zero_add]
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
        have hab : (Fi.card : ℝ) ≤ (((Fi.filter fun x => near (θ x.2) 0 0)).card : ℝ) +
            (((Fi.filter fun x => near (θ x.2) π 0)).card : ℝ) := by exact_mod_cast a.trans b
        linarith
      have hWi : ∀ x ∈ Fi, W H x.1 (θ x.2) ≤ 4 * Real.sqrt (54 * H / Real.sqrt X) := by
        intro x hx
        refine (hW x (Finset.mem_filter.mp hx).1).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.sqrt_le_sqrt
        apply div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr (by linarith))
        exact Real.sqrt_le_sqrt (hmem x hx).1
      have hX : Real.sqrt X * Real.sqrt (54 * H / Real.sqrt X) =
          Real.sqrt 54 * Real.sqrt H * q ^ i := by
        have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
        rw [← Real.sqrt_mul (by positivity)]
        rw [show X * (54 * H / Real.sqrt X) = 54 * H * Real.sqrt X by
          field_simp; rw [Real.sq_sqrt (by linarith)]]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
        congr 1
        simp only [X, q]
        rw [sqrt_pow' (by norm_num), sqrt_pow' (Real.sqrt_nonneg _)]
      calc ∑ x ∈ Fi, W H x.1 (θ x.2) ≤ ∑ _x ∈ Fi, 4 * Real.sqrt (54 * H / Real.sqrt X) :=
            Finset.sum_le_sum hWi
        _ = Fi.card * (4 * Real.sqrt (54 * H / Real.sqrt X)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * Ks * Real.sqrt X * (3 * Real.log H)) * (4 * Real.sqrt (54 * H / Real.sqrt X)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 24 * Ks * Real.log H * (Real.sqrt X * Real.sqrt (54 * H / Real.sqrt X)) := by ring
        _ = _ := by rw [hX]; ring
  refine (Finset.sum_le_sum hband).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (I + 1)) 0,
    if_pos (Finset.mem_range.mpr (by omega)), ← Finset.mul_sum]
  -- the geometric sum
  have hgeo := geom_le (by linarith : 1 < q) I
  have hqI : q ^ (I + 1) ≤ Real.sqrt 2 * Real.sqrt H := by
    have h2I : (2 : ℝ) ^ I ≤ 2 * H ^ 2 := by
      have := Nat.pow_log_le_self 2 (show Nmax H ≠ 0 by
        have : 1 ≤ Nmax H := Nat.le_floor (by push_cast; nlinarith)
        omega)
      exact (by exact_mod_cast this : (2 : ℝ) ^ I ≤ Nmax H).trans (Nmax_le hH)
    have hqi : q ^ I = Real.sqrt (Real.sqrt ((2 : ℝ) ^ I)) := by
      simp only [q]; rw [sqrt_pow' (by norm_num), sqrt_pow' (Real.sqrt_nonneg _)]
    have hq2 : q ^ 2 = Real.sqrt 2 := Real.sq_sqrt (Real.sqrt_nonneg _)
    have : q ^ I ≤ q * Real.sqrt H := by
      rw [hqi]
      have : Real.sqrt (Real.sqrt ((2 : ℝ) ^ I)) ≤ Real.sqrt (Real.sqrt (2 * H ^ 2)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h2I)
      refine this.trans (le_of_eq ?_)
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith), Real.sqrt_mul
        (Real.sqrt_nonneg _)]
    calc q ^ (I + 1) = q * q ^ I := by ring
      _ ≤ q * (q * Real.sqrt H) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = q ^ 2 * Real.sqrt H := by ring
      _ = _ := by rw [hq2]
  have hq1 : 0 < q - 1 := by linarith
  have hsum : ∑ i ∈ Finset.range (I + 1), q ^ i ≤ Real.sqrt 2 / (q - 1) * Real.sqrt H := by
    refine hgeo.trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hqI hq1.le
  have hsH : Real.sqrt H * Real.sqrt H = H := Real.mul_self_sqrt (by linarith)
  have hsH1 : 1 ≤ Real.sqrt H := by rw [Real.le_sqrt' (by norm_num)]; linarith
  have hA : 0 ≤ 24 * Ks * Real.log H * (Real.sqrt 54 * Real.sqrt H) := by
    have : 0 ≤ Real.log H := by linarith
    positivity
  calc 4 * K₀ * (Real.sqrt 54 * Real.sqrt H) +
        24 * Ks * Real.log H * (Real.sqrt 54 * Real.sqrt H) * ∑ i ∈ Finset.range (I + 1), q ^ i
      ≤ 4 * K₀ * (Real.sqrt 54 * Real.sqrt H) +
        24 * Ks * Real.log H * (Real.sqrt 54 * Real.sqrt H) *
          (Real.sqrt 2 / (q - 1) * Real.sqrt H) := by
        gcongr
    _ = 4 * K₀ * Real.sqrt 54 * Real.sqrt H +
        24 * Ks * Real.sqrt 54 * (Real.sqrt 2 / (q - 1)) * Real.log H *
          (Real.sqrt H * Real.sqrt H) := by ring
    _ = 4 * K₀ * Real.sqrt 54 * Real.sqrt H +
        24 * Ks * Real.sqrt 54 * (Real.sqrt 2 / (q - 1)) * Real.log H * H := by rw [hsH]
    _ ≤ (4 * K₀ * Real.sqrt 54 + 48 * Ks * Real.sqrt 54 * (Real.sqrt 2 / (q - 1))) * H *
          Real.log H := by
        have hsHH : Real.sqrt H ≤ H * Real.log H := by nlinarith
        have h1 : 4 * K₀ * Real.sqrt 54 * Real.sqrt H ≤ 4 * K₀ * Real.sqrt 54 * (H * Real.log H) :=
          mul_le_mul_of_nonneg_left hsHH (by positivity)
        have h2 : 0 ≤ 24 * Ks * Real.sqrt 54 * (Real.sqrt 2 / (q - 1)) * Real.log H * H := by
          have : 0 ≤ Real.log H := by linarith
          positivity
        nlinarith

end Cubic.BoxAsymptotic.Bands
