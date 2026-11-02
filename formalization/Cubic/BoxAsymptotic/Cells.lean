import Cubic.BoxAsymptotic.Core
import Cubic.BoxAsymptotic.DyadicCount

/-!
# Band–angle cells (the band estimates of `lem:geometry`)

For a band `2^i ≤ n < 2^{i+1}` (`X = 2^i ≥ 2`) and a centre `θ₀ ∈ {0, π}`, let `τ` be the
distance of `arg β` to the nearer of `0, π`.

* On a sector `τ_{θ₀} ≤ T` there are `≤ K (TX + √X) log X` pairs and `W ≤ 4√(54H/√X)`.
* On a cell `T ≤ τ ≤ 2T` with `T² X √X ≥ 134 H`, `W ≤ 500 H/(XT)` (`W_le_away`, with
  `1 - |cos θ| ≥ 2τ²/π²`), so the cell carries `≤ K (2TX + √X) log X · 500 H/(XT)`.

These are the draft's bounds `W ≪ H^{1/2} X^{-1/4}` and `W ≪ H/(Xτ)` combined with
`lem:sector` (`eq:bandupper`).
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Cells

open Real
open CubicTargets.BoxAsymptotic (wrap)
open Cubic.BoxAsymptotic.AngularSpacing (near)
open Cubic.BoxAsymptotic.Admissible (Bset θ mem_Bset Nmax)
open Cubic.BoxAsymptotic.Bands (band band_bounds sector)
open Cubic.BoxAsymptotic.TraceWidth (W W_le_sqrt W_le_away W_nonneg)
open Cubic.BoxAsymptotic.Pieces (τof)
open Cubic.BoxAsymptotic.Core (tau_sum)
open scoped Classical

theorem near_of_tau {t θ₀ T : ℝ} (h : τof θ₀ t ≤ T) : near t θ₀ T := by
  refine ⟨toIocDiv two_pi_pos (-π) (t - θ₀), ?_⟩
  have e : t - θ₀ - 2 * π * (toIocDiv two_pi_pos (-π) (t - θ₀) : ℝ) = wrap (t - θ₀) := by
    simp only [wrap, toIocMod, zsmul_eq_mul]; ring
  rw [e]; exact h

/-- The distance to the nearer centre. -/
def τmin (t : ℝ) : ℝ := min (τof 0 t) (τof π t)

theorem τmin_le (t : ℝ) : τmin t ≤ π / 2 := by
  have := tau_sum t
  simp only [τmin]
  rcases le_total (τof 0 t) (τof π t) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem cos_τmin (t : ℝ) : |Real.cos t| = Real.cos (τmin t) := by
  have h0 := (Cubic.BoxAsymptotic.BulkW.cos_τ t).1
  have hπ := (Cubic.BoxAsymptotic.BulkW.cos_τ t).2
  rw [sub_zero] at h0
  rw [Real.cos_sub_pi] at hπ
  have hs := tau_sum t
  have ha0 := abs_nonneg (wrap (t - 0))
  have haπ := abs_nonneg (wrap (t - π))
  have hτ0 : 0 ≤ τof 0 t := abs_nonneg _
  have hτπ : 0 ≤ τof π t := abs_nonneg _
  simp only [τmin]
  rcases le_total (τof 0 t) (τof π t) with h | h
  · rw [min_eq_left h, h0, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)]
  · rw [min_eq_right h, show Real.cos t = -Real.cos (τof π t) by linarith, abs_neg,
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)]


theorem one_sub_abs_cos_ge (t : ℝ) : 2 * τmin t ^ 2 / π ^ 2 ≤ 1 - |Real.cos t| := by
  rw [cos_τmin]
  have h0 : 0 ≤ τmin t := le_min (abs_nonneg _) (abs_nonneg _)
  exact Cubic.BoxAsymptotic.Bands.one_sub_cos_ge
    (by rw [abs_of_nonneg h0]; linarith [τmin_le t, Real.pi_pos])

/-- `W` on a non-critical cell. -/
theorem W_cell {H n t X T : ℝ} (hH : 0 < H) (hX : 0 < X) (hXn : X ≤ n) (hT : 0 < T)
    (hτ : T ≤ τmin t) (hc : 134 * H ≤ T ^ 2 * (X * Real.sqrt X)) :
    W H n t ≤ 500 * H / (X * T) := by
  have hn : 0 < n := lt_of_lt_of_le hX hXn
  set c := 1 - |Real.cos t|
  have hpi := Cubic.BoxAsymptotic.BulkW.pi_sq_lt
  have hpi0 : 0 < π ^ 2 := by positivity
  have hcT : 2 * T ^ 2 / π ^ 2 ≤ c := by
    refine le_trans ?_ (one_sub_abs_cos_ge t)
    apply div_le_div_of_nonneg_right _ hpi0.le
    nlinarith
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hcT
  have hsX : Real.sqrt X ≤ Real.sqrt n := Real.sqrt_le_sqrt hXn
  have hn3 : X * Real.sqrt X ≤ Real.sqrt n ^ 3 := by
    rw [pow_succ, Real.sq_sqrt hn.le]
    exact mul_le_mul hXn hsX (Real.sqrt_nonneg _) hn.le
  have hbig : 27 * H ≤ Real.sqrt n ^ 3 * c := by
    have : T ^ 2 * (X * Real.sqrt X) * (2 / π ^ 2) ≤ Real.sqrt n ^ 3 * c := by
      have e : T ^ 2 * (X * Real.sqrt X) * (2 / π ^ 2) = (X * Real.sqrt X) * (2 * T ^ 2 / π ^ 2) := by
        ring
      rw [e]; exact mul_le_mul hn3 hcT (by positivity) (by positivity)
    have : 27 * H ≤ 134 * H * (2 / π ^ 2) := by
      rw [show 134 * H * (2 / π ^ 2) = 268 * H / π ^ 2 by ring, le_div_iff₀ hpi0]
      nlinarith
    have : 134 * H * (2 / π ^ 2) ≤ T ^ 2 * (X * Real.sqrt X) * (2 / π ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  refine (W_le_away hn hH.le hc0 hbig).trans ?_
  -- `216 H/(n √c) ≤ 500 H/(X T)`
  have hsc : Real.sqrt 2 * T / π ≤ Real.sqrt c := by
    rw [Real.le_sqrt (by positivity) hc0.le, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hs2 : 1.414 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpi' := Real.pi_lt_d2
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : X * (Real.sqrt 2 * T / π) ≤ n * Real.sqrt c :=
    mul_le_mul hXn hsc (by positivity) hn.le
  have h2 : 216 * H * (X * T) * π ≤ 500 * H * (X * (Real.sqrt 2 * T)) := by
    have : 0 ≤ H * (X * T) := by positivity
    nlinarith
  have h3 : 500 * H * (X * (Real.sqrt 2 * T / π)) ≤ 500 * H * (n * Real.sqrt c) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e : 500 * H * (X * (Real.sqrt 2 * T / π)) * π = 500 * H * (X * (Real.sqrt 2 * T)) := by
    field_simp
  have hpi0' : 0 < π := Real.pi_pos
  nlinarith

/-- `W ≤ 4 √(54 H/√X)` in a band. -/
theorem W_crit {H n t X : ℝ} (hH : 0 ≤ H) (hX : 0 < X) (hXn : X ≤ n) :
    W H n t ≤ 4 * Real.sqrt (54 * H / Real.sqrt X) := by
  refine (W_le_sqrt (lt_of_lt_of_le hX hXn)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hXn)


/-- A dyadic range `A ≤ c 2^k ≤ B` holds for at most `max(0, log₂(B/A)) + 1` values of `k`. -/
theorem count_range {A B c : ℝ} (hA : 0 < A) (S : Finset ℕ)
    (hS : ∀ k ∈ S, A ≤ c * 2 ^ k ∧ c * 2 ^ k ≤ B) :
    (S.card : ℝ) ≤ max 0 (Real.logb 2 (B / A)) + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; linarith [le_max_left 0 (Real.logb 2 (B / A))]
  set k₁ := S.min' hne
  set k₂ := S.max' hne
  have h1 := (hS k₁ (S.min'_mem hne)).1
  have h2 := (hS k₂ (S.max'_mem hne)).2
  have hk : k₁ ≤ k₂ := S.min'_le _ (S.max'_mem hne)
  have hsub : S ⊆ Finset.Icc k₁ k₂ := fun k hk' =>
    Finset.mem_Icc.mpr ⟨S.min'_le k hk', S.le_max' k hk'⟩
  have hcard : (S.card : ℝ) ≤ (k₂ - k₁ : ℕ) + 1 := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    have : S.card ≤ k₂ - k₁ + 1 := by omega
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ (k₂ - k₁) ≤ B / A := by
    rw [le_div_iff₀ hA]
    have e : (2 : ℝ) ^ k₂ = 2 ^ (k₂ - k₁) * 2 ^ k₁ := by rw [← pow_add, Nat.sub_add_cancel hk]
    have : c * 2 ^ k₂ = 2 ^ (k₂ - k₁) * (c * 2 ^ k₁) := by rw [e]; ring
    rw [this] at h2
    calc (2 : ℝ) ^ (k₂ - k₁) * A ≤ 2 ^ (k₂ - k₁) * (c * 2 ^ k₁) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ B := h2
  have hBA : 0 < B / A := lt_of_lt_of_le (by positivity) hpow
  have hlog : ((k₂ - k₁ : ℕ) : ℝ) ≤ Real.logb 2 (B / A) :=
    (DyadicCount.two_pow_le_iff hBA _).mp hpow
  linarith [le_max_right 0 (Real.logb 2 (B / A))]


/-- The critical angle `T_c = √(134 H/(X √X))`. -/
def Tc (H X : ℝ) : ℝ := Real.sqrt (134 * H / (X * Real.sqrt X))

theorem Tc_pos {H X : ℝ} (hH : 0 < H) (hX : 0 < X) : 0 < Tc H X := by
  unfold Tc; positivity

theorem Tc_sq {H X : ℝ} (hH : 0 < H) (hX : 0 < X) : Tc H X ^ 2 * (X * Real.sqrt X) = 134 * H := by
  unfold Tc; rw [Real.sq_sqrt (by positivity)]; field_simp

/-- The cell index of a non-critical pair. -/
def cellIdx (H : ℝ) (x : ℕ × (ℤ × ℤ)) : ℕ :=
  Nat.log 2 ⌊τmin (θ x.2) / Tc H (2 ^ band x)⌋₊

theorem cellIdx_spec {H : ℝ} (hH : 0 < H) {x : ℕ × (ℤ × ℤ)}
    (h : Tc H (2 ^ band x) < τmin (θ x.2)) :
    Tc H (2 ^ band x) * 2 ^ cellIdx H x ≤ τmin (θ x.2) ∧
      τmin (θ x.2) ≤ 2 * (Tc H (2 ^ band x) * 2 ^ cellIdx H x) := by
  set T := Tc H (2 ^ band x)
  have hT : 0 < T := Tc_pos hH (by positivity)
  set q := τmin (θ x.2) / T
  have hq : 1 < q := by rw [lt_div_iff₀ hT]; linarith
  have hfl : ⌊q⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊q⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  have h1 := Nat.pow_log_le_self 2 hfl
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊q⌋₊
  have a : (2 : ℝ) ^ cellIdx H x ≤ q :=
    (by exact_mod_cast h1 : ((2 ^ cellIdx H x : ℕ) : ℝ) ≤ ⌊q⌋₊).trans (Nat.floor_le (by linarith))
      |>.trans_eq' (by push_cast; rfl)
  have b : q < (2 : ℝ) ^ (cellIdx H x + 1) := by
    have : (⌊q⌋₊ : ℝ) + 1 ≤ 2 ^ (cellIdx H x + 1) := by exact_mod_cast h2
    linarith [Nat.lt_floor_add_one q]
  constructor
  · rw [le_div_iff₀ hT] at a; linarith
  · rw [div_lt_iff₀ hT, pow_succ] at b; linarith


/-- Two-centre sector count within a band. -/
theorem two_sector {Ks : ℝ}
    (hsec : ∀ (H X θ₀ Θ : ℝ), 2 ≤ X → 0 ≤ Θ → ∀ F : Finset (ℕ × (ℤ × ℤ)), F ⊆ Bset H →
      (∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ near (θ x.2) θ₀ Θ) →
      (F.card : ℝ) ≤ Ks * (Θ * X + Real.sqrt X) * Real.log X)
    {H X Θ : ℝ} (hX : 2 ≤ X) (hΘ : 0 ≤ Θ) (F : Finset (ℕ × (ℤ × ℤ))) (hF : F ⊆ Bset H)
    (hmem : ∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ τmin (θ x.2) ≤ Θ) :
    (F.card : ℝ) ≤ 2 * (Ks * (Θ * X + Real.sqrt X) * Real.log X) := by
  have hsub : F ⊆ (F.filter fun x => τof 0 (θ x.2) ≤ Θ) ∪ (F.filter fun x => τof π (θ x.2) ≤ Θ) := by
    intro x hx
    have h := (hmem x hx).2.2
    simp only [τmin] at h
    rcases le_total (τof 0 (θ x.2)) (τof π (θ x.2)) with hl | hl
    · rw [min_eq_left hl] at h
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
    · rw [min_eq_right hl] at h
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hc : ∀ θ₀, (((F.filter fun x => τof θ₀ (θ x.2) ≤ Θ)).card : ℝ) ≤
      Ks * (Θ * X + Real.sqrt X) * Real.log X := fun θ₀ =>
    hsec H X θ₀ Θ hX hΘ _ (fun x hx => hF (Finset.mem_filter.mp hx).1) fun x hx =>
      ⟨(hmem x (Finset.mem_filter.mp hx).1).1, (hmem x (Finset.mem_filter.mp hx).1).2.1,
        near_of_tau (Finset.mem_filter.mp hx).2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h' : (F.card : ℝ) ≤ (((F.filter fun x => τof 0 (θ x.2) ≤ Θ)).card : ℝ) +
      (((F.filter fun x => τof π (θ x.2) ≤ Θ)).card : ℝ) := by exact_mod_cast this
  linarith [hc 0, hc π]

/-- **The band bound**: a band splits into the critical sector and dyadic cells. -/
theorem band_bound {Ks : ℝ}
    (hsec : ∀ (H X θ₀ Θ : ℝ), 2 ≤ X → 0 ≤ Θ → ∀ F : Finset (ℕ × (ℤ × ℤ)), F ⊆ Bset H →
      (∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X ∧ near (θ x.2) θ₀ Θ) →
      (F.card : ℝ) ≤ Ks * (Θ * X + Real.sqrt X) * Real.log X)
    {H : ℝ} (hH : 3 ≤ H) {i : ℕ} (hi : 1 ≤ i) (F : Finset (ℕ × (ℤ × ℤ))) (hF : F ⊆ Bset H)
    (hb : ∀ x ∈ F, band x = i) :
    ∑ x ∈ F, W H x.1 (θ x.2) ≤
      2 * (Ks * (Tc H (2 ^ i) * 2 ^ i + Real.sqrt (2 ^ i)) * Real.log (2 ^ i)) *
          (4 * Real.sqrt (54 * H / Real.sqrt (2 ^ i))) +
        ∑ k ∈ (F.filter fun x => Tc H (2 ^ i) < τmin (θ x.2)).image (cellIdx H),
          2 * (Ks * (2 * (Tc H (2 ^ i) * 2 ^ k) * 2 ^ i + Real.sqrt (2 ^ i)) * Real.log (2 ^ i)) *
            (500 * H / (2 ^ i * (Tc H (2 ^ i) * 2 ^ k))) := by
  have hH0 : 0 < H := by linarith
  set X : ℝ := 2 ^ i with hXdef
  have hX2 : 2 ≤ X := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
    simpa [X] using this
  have hX0 : 0 < X := by linarith
  set T := Tc H X
  have hT : 0 < T := Tc_pos hH0 hX0
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hmem : ∀ x ∈ F, X ≤ x.1 ∧ (x.1 : ℝ) ≤ 2 * X := by
    intro x hx
    have h1 := (mem_Bset.mp (by simpa using hF hx : (x.1, x.2) ∈ Bset H)).1
    have hbb := band_bounds h1
    rw [hb x hx] at hbb
    exact ⟨hbb.1, by rw [pow_succ] at hbb; linarith [hbb.2]⟩
  rw [← Finset.sum_filter_add_sum_filter_not F (fun x => τmin (θ x.2) ≤ T)]
  refine add_le_add ?_ ?_
  · -- critical sector
    set Fc := F.filter fun x => τmin (θ x.2) ≤ T
    have hcard := two_sector hsec hX2 hT.le Fc (fun x hx => hF (Finset.mem_filter.mp hx).1)
      fun x hx => ⟨(hmem x (Finset.mem_filter.mp hx).1).1,
        (hmem x (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩
    calc ∑ x ∈ Fc, W H x.1 (θ x.2) ≤ ∑ _x ∈ Fc, 4 * Real.sqrt (54 * H / Real.sqrt X) :=
          Finset.sum_le_sum fun x hx =>
            W_crit hH0.le hX0 (hmem x (Finset.mem_filter.mp hx).1).1
      _ = Fc.card * (4 * Real.sqrt (54 * H / Real.sqrt X)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  · -- cells
    set Fn := F.filter fun x => ¬ τmin (θ x.2) ≤ T
    have hFn : Fn = F.filter fun x => T < τmin (θ x.2) := by
      simp only [Fn, not_le]
    rw [hFn, ← Finset.sum_fiberwise_of_maps_to (g := cellIdx H)
      (t := (F.filter fun x => T < τmin (θ x.2)).image (cellIdx H))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_le_sum fun k _ => ?_
    set Fk := (F.filter fun x => T < τmin (θ x.2)).filter fun x => cellIdx H x = k
    have hFk : ∀ x ∈ Fk, x ∈ F ∧ T * 2 ^ k ≤ τmin (θ x.2) ∧ τmin (θ x.2) ≤ 2 * (T * 2 ^ k) := by
      intro x hx
      obtain ⟨hx1, hk⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxF, hTx⟩ := Finset.mem_filter.mp hx1
      have hbx := hb x hxF
      have hTx' : Tc H (2 ^ band x) < τmin (θ x.2) := by rw [hbx]; exact hTx
      have := cellIdx_spec hH0 hTx'
      rw [hbx, hk] at this
      exact ⟨hxF, this⟩
    have hTk : 0 < T * 2 ^ k := by positivity
    have hcard := two_sector hsec hX2 (by positivity : (0 : ℝ) ≤ 2 * (T * 2 ^ k)) Fk
      (fun x hx => hF (hFk x hx).1) fun x hx =>
        ⟨(hmem x (hFk x hx).1).1, (hmem x (hFk x hx).1).2, (hFk x hx).2.2⟩
    have hWk : ∀ x ∈ Fk, W H x.1 (θ x.2) ≤ 500 * H / (X * (T * 2 ^ k)) := by
      intro x hx
      obtain ⟨hxF, h1, -⟩ := hFk x hx
      refine W_cell hH0 hX0 (hmem x hxF).1 hTk h1 ?_
      have hsq := Tc_sq hH0 hX0
      have : T ^ 2 ≤ (T * 2 ^ k) ^ 2 := by
        apply pow_le_pow_left₀ hT.le
        exact le_mul_of_one_le_right hT.le (one_le_pow₀ (by norm_num))
      have hXX : 0 ≤ X * Real.sqrt X := by positivity
      nlinarith
    calc ∑ x ∈ Fk, W H x.1 (θ x.2) ≤ ∑ _x ∈ Fk, 500 * H / (X * (T * 2 ^ k)) :=
          Finset.sum_le_sum hWk
      _ = Fk.card * (500 * H / (X * (T * 2 ^ k))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Cubic.BoxAsymptotic.Cells
