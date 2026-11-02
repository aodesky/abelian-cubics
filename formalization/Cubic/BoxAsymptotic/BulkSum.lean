import Cubic.BoxAsymptotic.GoodSums

/-!
# The bulk: `Σ_n ∫ W w_bulk dμ_n` via `SmoothSectorCounting`

`w_bulk(n, θ) = Σ_{θ₀ ∈ {0, π}} Σ_{good (i, j)} φ(n/2^i) φ(τ_{θ₀}/2^{-j})`. On each piece,
`W = 18√3 H/(nτ) (1 + O(ε))` (`BulkW.W_compare`), and `Σ_{(n, β)} 18√3 H/(nτ) φ φ` is
evaluated by `Pieces.piece`, with main term

  `M(i) = 18√3 (log 2/π) H ((a log 2^i + b₀) log 2 + a c₁)`

per piece (independent of `j` and `θ₀`) and error `≤ 6 (H/(XΘ)) |Cst| √X (3 log H)^{A'}`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.BulkSum

open Real
open CubicTargets.BoxAsymptotic (aStar muIntegral weight wrap)
open Cubic.BoxAsymptotic.Admissible (Bset Nmax θ mem_Bset)
open Cubic.BoxAsymptotic.TraceWidth (W W_nonneg)
open Cubic.BoxAsymptotic.SmoothPartition (φ Φ Ψ φ_support φ_nonneg)
open Cubic.BoxAsymptotic.PartitionIntegrals (c₁)
open Cubic.BoxAsymptotic.Pieces (τof pw pw_nonneg piece)
open Cubic.BoxAsymptotic.BulkW (Good W_compare W_sub_pi cos_τ)
open Cubic.BoxAsymptotic.GoodSet (G mem_G)
open Cubic.BoxAsymptotic.GoodSums (X Θ sum_good)
open scoped Classical

/-- The main term of one piece. -/
def M (H b₀ : ℝ) (i : ℕ) : ℝ :=
  18 * Real.sqrt 3 * (Real.log 2 / Real.pi) * H *
    ((aStar * Real.log (2 ^ i) + b₀) * Real.log 2 + aStar * c₁)

/-- The bulk weight with centre `θ₀`. -/
def wb (H ε θ₀ n t : ℝ) : ℝ := ∑ p ∈ G H ε, pw (X p) (Θ p) θ₀ n t

/-- The support of a piece. -/
theorem supp_of_pw {Xv Θv θ₀ n t : ℝ} (hX : 0 < Xv) (hΘ : 0 < Θv) (h : pw Xv Θv θ₀ n t ≠ 0) :
    Xv / 2 ≤ n ∧ n ≤ 2 * Xv ∧ Θv / 2 ≤ τof θ₀ t ∧ τof θ₀ t ≤ 2 * Θv := by
  have h1 : φ (n / Xv) ≠ 0 := fun h0 => h (by simp [pw, h0])
  have h2 : φ (τof θ₀ t / Θv) ≠ 0 := fun h0 => h (by simp [pw, h0])
  have a := φ_support h1
  have b := φ_support h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (le_div_iff₀ hX).mp a.1; linarith
  · exact (div_le_iff₀ hX).mp a.2
  · have := (le_div_iff₀ hΘ).mp b.1; linarith
  · exact (div_le_iff₀ hΘ).mp b.2

/-- `W` against `18√3 H/(nτ)` on a piece, for `θ₀ ∈ {0, π}`. -/
theorem piece_W {H ε θ₀ : ℝ} {p : ℕ × ℕ} (hp : Good H ε p.1 p.2) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hH : 1 ≤ H) (hθ₀ : θ₀ = 0 ∨ θ₀ = Real.pi) (n t : ℝ) :
    |W H n t * pw (X p) (Θ p) θ₀ n t -
        18 * Real.sqrt 3 * H / (n * τof θ₀ t) * pw (X p) (Θ p) θ₀ n t| ≤
      14 * ε * (18 * Real.sqrt 3 * H / (n * τof θ₀ t) * pw (X p) (Θ p) θ₀ n t) := by
  by_cases h0 : pw (X p) (Θ p) θ₀ n t = 0
  · simp [h0]
  have hX : 0 < X p := by simp only [X]; positivity
  have hΘ : 0 < Θ p := by simp only [Θ]; positivity
  obtain ⟨h1, h2, h3, h4⟩ := supp_of_pw hX hΘ h0
  have hpw := pw_nonneg (X p) (Θ p) θ₀ n t
  rw [← sub_mul, abs_mul, abs_of_nonneg hpw, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hpw
  rcases hθ₀ with rfl | rfl
  · exact W_compare hp hε0 hε1 hH h1 h2 h3 h4 (by rw [← (cos_τ t).1]; simp)
  · rw [← W_sub_pi]
    exact W_compare hp hε0 hε1 hH h1 h2 h3 h4 (cos_τ t).2


/-- The log factor on a good piece: `1 ≤ log(2X + 1/Θ) ≤ 3 log H`. -/
theorem log_factor {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) {p : ℕ × ℕ}
    (hp : Good H ε p.1 p.2) :
    1 ≤ Real.log (2 * X p + 1 / Θ p) ∧ Real.log (2 * X p + 1 / Θ p) ≤ 3 * Real.log H := by
  have hj := Cubic.BoxAsymptotic.GoodSet.two_pow_le hH hε0 hε1 hp
  have h4 : 16 * X p ≤ H ^ 2 := hp.g4
  have hX2 : 2 ≤ X p := by
    simp only [X]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ p.1 := pow_le_pow_right₀ (by norm_num) hp.hi
    simpa using this
  have hΘ : 1 / Θ p = (2 : ℝ) ^ p.2 := by simp only [Θ]; rw [one_div_pow, one_div_one_div]
  have hj4 : (4 : ℝ) ≤ 2 ^ p.2 := by
    have : (2 : ℝ) ^ 2 ≤ 2 ^ p.2 := pow_le_pow_right₀ (by norm_num) hp.hj
    norm_num at this; exact this
  rw [hΘ]
  constructor
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  · have : 2 * X p + 2 ^ p.2 ≤ H ^ 2 := by nlinarith
    calc Real.log (2 * X p + 2 ^ p.2) ≤ Real.log (H ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log H := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 3 * Real.log H := by
          have : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
          linarith

theorem rpow_le {y A L : ℝ} (hy1 : 1 ≤ y) (hyL : y ≤ L) :
    y ^ A ≤ L ^ (max A 0) :=
  (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left A 0)).trans
    (Real.rpow_le_rpow (by linarith) hyL (le_max_right A 0))

/-- **The bulk**. -/
theorem bulk {H ε b₀ A Cst : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hd : ∀ X Θ θ₀ : ℝ, 2 ≤ X → 0 < Θ → Θ ≤ 1 / 4 →
      |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (weight Φ Ψ X Θ θ₀ n)) -
        Θ * Real.log 2 / Real.pi * X * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁)| ≤
      Cst * Real.sqrt X * Real.log (2 * X + 1 / Θ) ^ A) :
    |(1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) *
        (wb H ε 0 x.1 (θ x.2) + wb H ε Real.pi x.1 (θ x.2))) - 2 * ∑ p ∈ G H ε, M H b₀ p.1| ≤
      28 * ε * ∑ p ∈ G H ε, |M H b₀ p.1| +
        (1 + 14 * ε) * 36 * Real.sqrt 3 * |Cst| * (3 * Real.log H) ^ (max A 0) * (ε ^ 2 * H / 500) := by
  have hH1 : (1 : ℝ) ≤ H := by linarith
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  set E := 6 * |Cst| * (3 * Real.log H) ^ (max A 0)
  have hE0 : 0 ≤ E := by positivity
  have h3 : 0 < Real.sqrt 3 := by positivity
  -- per piece and centre
  have hpiece : ∀ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = Real.pi) → ∀ p ∈ G H ε,
      |(1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)) - M H b₀ p.1| ≤
        3 * Real.sqrt 3 * (1 + 14 * ε) * (E * (H / (X p * Θ p) * Real.sqrt (X p))) +
          14 * ε * |M H b₀ p.1| := by
    intro θ₀ hθ₀ p hp
    have hg := mem_G hp
    have hX2 : 2 ≤ X p := by
      simp only [X]
      have : (2 : ℝ) ^ 1 ≤ 2 ^ p.1 := pow_le_pow_right₀ (by norm_num) hg.hi
      simpa using this
    have hΘ0 : 0 < Θ p := by simp only [Θ]; positivity
    have hΘ4 : Θ p ≤ 1 / 4 := by
      simp only [Θ]
      calc ((1 : ℝ) / 2) ^ p.2 ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hg.hj
        _ = 1 / 4 := by norm_num
    have hXN : 2 * X p ≤ Nmax H := by
      have h4 : 16 * X p ≤ H ^ 2 := hg.g4
      have : H ^ 2 + 3 * H - 1 < (Nmax H : ℝ) := by
        have := Nat.lt_floor_add_one (H ^ 2 + 3 * H); simp only [Nmax]; linarith
      nlinarith
    have hpc := piece (H := H) hX2 hΘ0 hΘ4 hXN (hd (X p) (Θ p) θ₀ hX2 hΘ0 hΘ4) (by linarith)
    set S := ∑ x ∈ Bset H, H / (x.1 * τof θ₀ (θ x.2)) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun x hx => by
      have := pw_nonneg (X p) (Θ p) θ₀ x.1 (θ x.2)
      have : 0 ≤ τof θ₀ (θ x.2) := abs_nonneg _
      positivity
    -- the log factor
    have hlog := log_factor hH hε0 hε1 hg
    have herr : 6 * H / (X p * Θ p) * (Cst * Real.sqrt (X p) * Real.log (2 * X p + 1 / Θ p) ^ A) ≤
        E * (H / (X p * Θ p) * Real.sqrt (X p)) := by
      have hr := rpow_le (A := A) hlog.1 hlog.2
      have hrp : 0 ≤ Real.log (2 * X p + 1 / Θ p) ^ A := Real.rpow_nonneg (by linarith [hlog.1]) _
      have : Cst * Real.sqrt (X p) * Real.log (2 * X p + 1 / Θ p) ^ A ≤
          |Cst| * Real.sqrt (X p) * (3 * Real.log H) ^ (max A 0) := by
        calc Cst * Real.sqrt (X p) * Real.log (2 * X p + 1 / Θ p) ^ A
            ≤ |Cst| * Real.sqrt (X p) * Real.log (2 * X p + 1 / Θ p) ^ A :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
                (Real.sqrt_nonneg _)) hrp
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
      have hc : 0 ≤ 6 * H / (X p * Θ p) := by positivity
      calc _ ≤ 6 * H / (X p * Θ p) * (|Cst| * Real.sqrt (X p) * (3 * Real.log H) ^ (max A 0)) :=
            mul_le_mul_of_nonneg_left this hc
        _ = E * (H / (X p * Θ p) * Real.sqrt (X p)) := by simp only [E]; ring
    -- `M = 3√3 · main`
    have hM : M H b₀ p.1 = 3 * Real.sqrt 3 * (6 * Real.log 2 / Real.pi * H *
        ((aStar * Real.log (X p) + b₀) * Real.log 2 + aStar * c₁)) := by
      simp only [M, X]; ring
    have ha : |3 * Real.sqrt 3 * S - M H b₀ p.1| ≤
        3 * Real.sqrt 3 * (E * (H / (X p * Θ p) * Real.sqrt (X p))) := by
      rw [hM, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hpc.trans herr) (by positivity)
    have hb : |(1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)) -
        3 * Real.sqrt 3 * S| ≤ 14 * ε * (3 * Real.sqrt 3 * S) := by
      have e : 3 * Real.sqrt 3 * S = (1 / 6) * ∑ x ∈ Bset H,
          18 * Real.sqrt 3 * H / (x.1 * τof θ₀ (θ x.2)) * pw (X p) (Θ p) θ₀ x.1 (θ x.2) := by
        simp only [S]; rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [e, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by norm_num)]
      rw [Finset.mul_sum, Finset.mul_sum]
      calc 1 / 6 * |∑ x ∈ Bset H, (W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2) -
            18 * Real.sqrt 3 * H / (x.1 * τof θ₀ (θ x.2)) * pw (X p) (Θ p) θ₀ x.1 (θ x.2))|
          ≤ 1 / 6 * ∑ x ∈ Bset H, |W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2) -
            18 * Real.sqrt 3 * H / (x.1 * τof θ₀ (θ x.2)) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
        _ ≤ 1 / 6 * ∑ x ∈ Bset H, 14 * ε * (18 * Real.sqrt 3 * H / (x.1 * τof θ₀ (θ x.2)) *
            pw (X p) (Θ p) θ₀ x.1 (θ x.2)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
              piece_W hg hε0 hε1 hH1 hθ₀ _ _) (by norm_num)
        _ = ∑ x ∈ Bset H, 14 * ε * (1 / 6 * (18 * Real.sqrt 3 * H / (x.1 * τof θ₀ (θ x.2)) *
            pw (X p) (Θ p) θ₀ x.1 (θ x.2))) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have hS : 3 * Real.sqrt 3 * S ≤ |M H b₀ p.1| +
        3 * Real.sqrt 3 * (E * (H / (X p * Θ p) * Real.sqrt (X p))) := by
      have := (abs_le.mp ha).2; linarith [le_abs_self (M H b₀ p.1)]
    have hε14 : 0 ≤ 14 * ε := by positivity
    calc |(1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)) -
          M H b₀ p.1|
        ≤ |(1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2)) -
            3 * Real.sqrt 3 * S| + |3 * Real.sqrt 3 * S - M H b₀ p.1| := abs_sub_le _ _ _
      _ ≤ 14 * ε * (3 * Real.sqrt 3 * S) +
            3 * Real.sqrt 3 * (E * (H / (X p * Θ p) * Real.sqrt (X p))) := add_le_add hb ha
      _ ≤ 14 * ε * (|M H b₀ p.1| + 3 * Real.sqrt 3 * (E * (H / (X p * Θ p) * Real.sqrt (X p)))) +
            3 * Real.sqrt 3 * (E * (H / (X p * Θ p) * Real.sqrt (X p))) := by
          have := mul_le_mul_of_nonneg_left hS hε14; linarith
      _ = _ := by ring
  -- sum over pieces and centres
  have hsplit : (1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) *
      (wb H ε 0 x.1 (θ x.2) + wb H ε Real.pi x.1 (θ x.2))) =
      ∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) 0 x.1 (θ x.2)) +
      ∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H,
        W H x.1 (θ x.2) * pw (X p) (Θ p) Real.pi x.1 (θ x.2)) := by
    simp only [wb, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Bset H), Finset.sum_comm (s := Bset H) (t := G H ε)]
  rw [hsplit]
  have h0 := fun p hp => hpiece 0 (Or.inl rfl) p hp
  have hπ := fun p hp => hpiece Real.pi (Or.inr rfl) p hp
  have hsum := sum_good hH hε0 hε1
  have key : ∀ θ₀ : ℝ, (θ₀ = 0 ∨ θ₀ = Real.pi) →
      |(∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) θ₀ x.1 (θ x.2))) -
        ∑ p ∈ G H ε, M H b₀ p.1| ≤
      3 * Real.sqrt 3 * (1 + 14 * ε) * (E * (ε ^ 2 * H / 500)) +
        14 * ε * ∑ p ∈ G H ε, |M H b₀ p.1| := by
    intro θ₀ hθ₀
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun p hp => hpiece θ₀ hθ₀ p hp).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have : 0 ≤ 3 * Real.sqrt 3 * (1 + 14 * ε) * E := by positivity
    have := mul_le_mul_of_nonneg_left hsum this
    nlinarith
  have k0 := key 0 (Or.inl rfl)
  have kπ := key Real.pi (Or.inr rfl)
  have e : (∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) 0 x.1 (θ x.2)) +
      ∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H,
        W H x.1 (θ x.2) * pw (X p) (Θ p) Real.pi x.1 (θ x.2))) - 2 * ∑ p ∈ G H ε, M H b₀ p.1 =
      ((∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H, W H x.1 (θ x.2) * pw (X p) (Θ p) 0 x.1 (θ x.2))) -
        ∑ p ∈ G H ε, M H b₀ p.1) +
      ((∑ p ∈ G H ε, (1 / 6) * (∑ x ∈ Bset H,
        W H x.1 (θ x.2) * pw (X p) (Θ p) Real.pi x.1 (θ x.2))) - ∑ p ∈ G H ε, M H b₀ p.1) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have : E * (ε ^ 2 * H / 500) = 6 * |Cst| * (3 * Real.log H) ^ (max A 0) * (ε ^ 2 * H / 500) := rfl
  nlinarith

end Cubic.BoxAsymptotic.BulkSum
