import Cubic.Counting.GeneralTraceDecomposition
import Cubic.Counting.TraceZeroAsymptotic
import Cubic.Counting.RiemannSum
import Cubic.Counting.GeneralMonicIntegrals
import Cubic.Counting.AsymptoticConstantIdentities
import Cubic.Counting.AsymptoticConstantsConvergence
import Cubic.Counting.AsymptoticPolynomialCount
import Cubic.Counting.MonicConstantsFromTraceCounts

/-!
# Proof of `thm:generalMonicCount`

Following the paper: by `eqn:generalTraceDecomposition`, the count is
`Σ_{|s| ≤ H, 3 ∤ s} A₁(3H² + s²) + Σ_{|s| ≤ H, 3 ∣ s} A₀(H² + s²/3)`. Insert `eqn:A1asymptotic`
and `prop:traceZeroAsymptotic`; the errors add up to `O_ε(H^{2+ε})`. With `u = s/H`,
`3H² + s² = H²(3 + u²)` and `H² + s²/3 = (H²/3)(3 + u²)`, so the main terms are Riemann sums
of `3 + u²` and `(3 + u²) log(3 + u²)` over the two residue classes `s ≢ 0 (mod 3)` and the
one class `s ≡ 0 (mod 3)`, with Riemann-sum errors `O(H² log H)`. The integrals are
`I = 𝒱_∞(1) = 20/3` and `J = 𝒱_∞'(1) = (40/3) log 2 + 4π√3/3 - 76/9`
(`eqn:monicArchimedeanMoments`). This gives the count with the trace-count coefficients
`C_mon = (220/81) C` and `D_mon` of `eqn:monicConstantsFromTraceCounts` (`trace_count`).
Finally the formulas for `C` and `D/C` in `thm:asymptoticPolynomialCount` give the displayed
constants.
-/

noncomputable section

namespace Cubic.Counting.GeneralMonicCount

open Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralMonicIntegrals
open CubicTargets.Counting.GeneralMonic

/-- `C_mon = (220/81) C`, the leading trace-count coefficient. -/
def Cmon : ℝ := 220 / 81 * Cconst

/-- The secondary trace-count coefficient, after `eqn:monicArchimedeanMoments`. -/
def Dmon : ℝ :=
  220 / 81 * Dconst + 220 / 81 * Cconst * Real.log 2 - 95 / 81 * Cconst * Real.log 3
    - 418 / 243 * Cconst + 22 * Real.pi * Real.sqrt 3 / 81 * Cconst
    - 20 * Real.pi * Real.sqrt 3 / 81

/-! ### Riemann sums over the traces -/

/-- The traces `|s| ≤ H`. -/
def T (H : ℝ) : Finset ℤ := Finset.Icc (-⌊H⌋) ⌊H⌋

section Riemann

variable {g : ℝ → ℝ} {M B : ℝ} (hg : Continuous g) (hM0 : 0 ≤ M)
  (hM : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2, |g x - g y| ≤ M * |x - y|)
  (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B)
include hg hM0 hM hB

/-- All traces: `Σ_{|s| ≤ H} g(s/H) = H ∫ g + O(1)`. -/
theorem riemann_all {H : ℝ} (hH : 1 ≤ H) :
    |∑ s ∈ T H, g (s / H) - H * ∫ u in (-1 : ℝ)..1, g u| ≤ 3 * M + 2 * B := by
  have hH0 : 0 < H := by linarith
  have h := Cubic.Counting.RiemannSum.riemann hg hM0 hM hB (δ := 1 / H) (N := ⌊H⌋₊)
    (by positivity) (by rw [div_le_one hH0]; exact hH)
    (by rw [mul_one_div, div_le_one hH0]; exact Nat.floor_le hH0.le)
    (by rw [mul_one_div, one_lt_div hH0]; exact Nat.lt_floor_add_one H)
  have hT : T H = Finset.Icc (-(⌊H⌋₊ : ℤ)) ⌊H⌋₊ := by
    rw [T, Int.natCast_floor_eq_floor hH0.le]
  rw [hT]
  have e : ∑ s ∈ Finset.Icc (-(⌊H⌋₊ : ℤ)) ⌊H⌋₊, g (s / H) - H * ∫ u in (-1 : ℝ)..1, g u =
      H * (1 / H * ∑ k ∈ Finset.Icc (-(⌊H⌋₊ : ℤ)) ⌊H⌋₊, g (k * (1 / H)) -
        ∫ u in (-1 : ℝ)..1, g u) := by
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel hH0.ne', one_mul]
    simp only [mul_one_div]
  rw [e, abs_mul, abs_of_pos hH0]
  calc H * _ ≤ H * ((3 * M + 2 * B) * (1 / H)) := mul_le_mul_of_nonneg_left h hH0.le
    _ = 3 * M + 2 * B := by field_simp

/-- Traces divisible by `3`: `Σ_{|s| ≤ H, 3 ∣ s} g(s/H) = (H/3) ∫ g + O(1)`. -/
theorem riemann_zero {H : ℝ} (hH : 3 ≤ H) :
    |∑ s ∈ (T H).filter (fun s => 3 ∣ s), g (s / H) - H / 3 * ∫ u in (-1 : ℝ)..1, g u| ≤
      3 * M + 2 * B := by
  have hH0 : 0 < H := by linarith
  have h := Cubic.Counting.RiemannSum.riemann hg hM0 hM hB (δ := 3 / H) (N := ⌊H / 3⌋₊)
    (by positivity) (by rw [div_le_one hH0]; exact hH)
    (by
      have := Nat.floor_le (by positivity : 0 ≤ H / 3)
      calc (⌊H / 3⌋₊ : ℝ) * (3 / H) ≤ H / 3 * (3 / H) := by gcongr
        _ = 1 := by field_simp)
    (by
      have := Nat.lt_floor_add_one (H / 3)
      calc (1 : ℝ) = H / 3 * (3 / H) := by field_simp
        _ < (⌊H / 3⌋₊ + 1) * (3 / H) := by gcongr)
  have hfl : ((⌊H / 3⌋₊ : ℕ) : ℤ) = ⌊H / 3⌋ := Int.natCast_floor_eq_floor (by positivity)
  have h1 : ∀ k : ℤ, 3 * k ≤ ⌊H⌋ ↔ k ≤ ⌊H / 3⌋ := by
    intro k
    rw [Int.le_floor, Int.le_floor, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]; push_cast
    constructor <;> intro h <;> linarith
  have key : ∀ k : ℤ, (-⌊H⌋ ≤ 3 * k ∧ 3 * k ≤ ⌊H⌋) ↔ (-⌊H / 3⌋ ≤ k ∧ k ≤ ⌊H / 3⌋) := by
    intro k
    have h2 := h1 (-k)
    rw [h1 k]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨by have := h2.mp (by omega); omega, hb⟩
    · rintro ⟨ha, hb⟩; exact ⟨by have := h2.mpr (by omega); omega, hb⟩
  have hsum : ∑ s ∈ (T H).filter (fun s => 3 ∣ s), g (s / H) =
      ∑ k ∈ Finset.Icc (-(⌊H / 3⌋₊ : ℤ)) ⌊H / 3⌋₊, g (k * (3 / H)) := by
    rw [hfl]
    refine Finset.sum_nbij' (fun s => s / 3) (fun k => 3 * k) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      simp only [T, Finset.mem_filter, Finset.mem_Icc] at hs ⊢
      obtain ⟨hs, k, rfl⟩ := hs
      rw [Int.mul_ediv_cancel_left _ (by norm_num)]
      exact (key k).mp hs
    · intro k hk
      simp only [T, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      exact ⟨(key k).mpr hk, dvd_mul_right _ _⟩
    · intro s hs
      simp only [T, Finset.mem_filter] at hs
      exact Int.mul_ediv_cancel' hs.2
    · intro k _
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    · intro s hs
      simp only [T, Finset.mem_filter] at hs
      obtain ⟨-, k, rfl⟩ := hs
      show g (((3 * k : ℤ) : ℝ) / H) = g ((((3 * k) / 3 : ℤ) : ℝ) * (3 / H))
      rw [Int.mul_ediv_cancel_left _ (by norm_num)]
      push_cast; ring_nf
  rw [hsum]
  have e : ∑ k ∈ Finset.Icc (-(⌊H / 3⌋₊ : ℤ)) ⌊H / 3⌋₊, g (k * (3 / H)) -
      H / 3 * ∫ u in (-1 : ℝ)..1, g u = H / 3 * (3 / H * ∑ k ∈ Finset.Icc (-(⌊H / 3⌋₊ : ℤ))
        ⌊H / 3⌋₊, g (k * (3 / H)) - ∫ u in (-1 : ℝ)..1, g u) := by
    rw [mul_sub, ← mul_assoc, show H / 3 * (3 / H) = 1 by field_simp, one_mul]
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < H / 3)]
  calc H / 3 * _ ≤ H / 3 * ((3 * M + 2 * B) * (3 / H)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 3 * M + 2 * B := by field_simp

end Riemann

/-! ### The main terms -/

theorem main_one (a b : ℝ) {H : ℝ} (hH : 0 < H) (s : ℤ) :
    a * (3 * H ^ 2 + (s : ℝ) ^ 2) * Real.log (3 * H ^ 2 + (s : ℝ) ^ 2) +
      b * (3 * H ^ 2 + (s : ℝ) ^ 2) =
      H ^ 2 * ((2 * a * Real.log H + b) * g₁ (s / H) + a * g₂ (s / H)) := by
  have hX : 3 * H ^ 2 + (s : ℝ) ^ 2 = H ^ 2 * g₁ (s / H) := by
    simp only [g₁]; field_simp
  rw [hX, Real.log_mul (by positivity) (g₁_pos _).ne', Real.log_pow]
  simp only [g₂, g₁]; push_cast; ring

theorem main_zero (a b : ℝ) {H : ℝ} (hH : 0 < H) (s : ℤ) :
    a * (H ^ 2 + (s : ℝ) ^ 2 / 3) * Real.log (H ^ 2 + (s : ℝ) ^ 2 / 3) +
      b * (H ^ 2 + (s : ℝ) ^ 2 / 3) =
      H ^ 2 / 3 * ((2 * a * Real.log H - a * Real.log 3 + b) * g₁ (s / H) + a * g₂ (s / H)) := by
  have hX : H ^ 2 + (s : ℝ) ^ 2 / 3 = H ^ 2 / 3 * g₁ (s / H) := by
    simp only [g₁]; field_simp
  rw [hX, Real.log_mul (by positivity) (g₁_pos _).ne', Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  simp only [g₂, g₁]; push_cast; ring

/-- The coefficients: `2I(2a₁/3 + a₀/9) = C_mon` and the `H³` coefficient is `D_mon`. -/
theorem coefficients (H L : ℝ) :
    H ^ 2 * ((2 * (Cconst / 6) * L + (Dconst / 3 - Real.pi / (9 * √3))) * (2 * H / 3 * (20 / 3)) +
      Cconst / 6 * (2 * H / 3 * (40 / 3 * Real.log 2 + 4 * Real.pi * √3 / 3 - 76 / 9))) +
    H ^ 2 / 3 * ((2 * (5 * Cconst / 6) * L - 5 * Cconst / 6 * Real.log 3 +
        (5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3 - Real.pi / (3 * √3))) * (H / 3 * (20 / 3)) +
      5 * Cconst / 6 * (H / 3 * (40 / 3 * Real.log 2 + 4 * Real.pi * √3 / 3 - 76 / 9))) =
    Cmon * H ^ 3 * L + Dmon * H ^ 3 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e1 : Real.pi / (9 * √3) = Real.pi * √3 / 27 := by
    field_simp; nlinarith [h3]
  have e2 : Real.pi / (3 * √3) = Real.pi * √3 / 9 := by
    field_simp; nlinarith [h3]
  rw [e1, e2]; simp only [Cmon, Dmon]; ring

/-! ### Error terms -/

theorem card_T_le {H : ℝ} (hH : 1 ≤ H) : ((T H).card : ℝ) ≤ 3 * H := by
  rw [T, Int.card_Icc]
  have h0 : 0 ≤ ⌊H⌋ := Int.floor_nonneg.mpr (by linarith)
  have : ((⌊H⌋ + 1 - -⌊H⌋).toNat : ℤ) = 2 * ⌊H⌋ + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have h' : (((⌊H⌋ + 1 - -⌊H⌋).toNat : ℕ) : ℝ) = 2 * (⌊H⌋ : ℝ) + 1 := by exact_mod_cast this
  rw [h']; linarith [Int.floor_le H]

theorem sq_le_of_mem {H : ℝ} {s : ℤ} (hs : s ∈ T H) : (s : ℝ) ^ 2 ≤ H ^ 2 := by
  have h := Cubic.Counting.GeneralTraceDecomposition.abs_le_of_mem hs
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Summing the errors of an expansion over the traces. -/
theorem sum_error_le {F : ℝ → ℝ} {K X₀ r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hK : ∀ X, X₀ ≤ X → |F X| ≤ K * X ^ r) {H : ℝ} (hH : 1 ≤ H) (hHX : X₀ ≤ c * H ^ 2)
    (arg : ℤ → ℝ) (harg : ∀ s ∈ T H, c * H ^ 2 ≤ arg s ∧ arg s ≤ 4 * H ^ 2)
    (S : Finset ℤ) (hS : S ⊆ T H) :
    |∑ s ∈ S, F (arg s)| ≤ S.card * (|K| * (4 * H ^ 2) ^ r) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun s hs => ?_
  obtain ⟨h1, h2⟩ := harg s (hS hs)
  have hpos : 0 < arg s := lt_of_lt_of_le (by positivity) h1
  refine (hK _ (hHX.trans h1)).trans ?_
  calc K * arg s ^ r ≤ |K| * arg s ^ r :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (4 * H ^ 2) ^ r :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos.le h2 hr.le) (abs_nonneg K)

theorem four_sq_rpow {H ε : ℝ} (hH : 0 < H) :
    (4 * H ^ 2) ^ (1 / 2 + ε / 2) = 4 ^ (1 / 2 + ε / 2) * H ^ (1 + ε) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast H 2,
    ← Real.rpow_mul hH.le]
  congr 2; push_cast; ring

/-- `|x d| ≤ |x| D` for `|d| ≤ D`. -/
theorem abs_mul_le_of {x d D : ℝ} (hd : |d| ≤ D) : |x * d| ≤ |x| * D := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd (abs_nonneg x)

/-- The errors of the expansions of `A₁` and `A₀`, summed over the traces, are
`O(H · H^{1+ε}) = O(H^{2+ε})`. -/
theorem errors_bound {F₁ F₀ : ℝ → ℝ} {K₁ K₀ X₁ X₀ ε H : ℝ} (hε : 0 < ε) (hH1 : 1 ≤ H)
    (h₁ : ∀ X, X₁ ≤ X → |F₁ X| ≤ K₁ * X ^ (1 / 2 + ε / 2))
    (h₀ : ∀ X, X₀ ≤ X → |F₀ X| ≤ K₀ * X ^ (1 / 2 + ε / 2)) (hX₁ : X₁ ≤ H ^ 2) (hX₀ : X₀ ≤ H ^ 2) :
    |∑ s ∈ (T H).filter (fun s => ¬ 3 ∣ s), F₁ (3 * H ^ 2 + (s : ℝ) ^ 2)| +
      |∑ s ∈ (T H).filter (fun s => 3 ∣ s), F₀ (H ^ 2 + (s : ℝ) ^ 2 / 3)| ≤
      3 * ((|K₁| + |K₀|) * 4 ^ (1 / 2 + ε / 2)) * H ^ (2 + ε) := by
  have hH0 : 0 < H := by linarith
  set T₁ := (T H).filter (fun s => ¬ 3 ∣ s)
  set T₀ := (T H).filter (fun s => 3 ∣ s)
  have hT₁ : T₁ ⊆ T H := Finset.filter_subset _ _
  have hT₀ : T₀ ⊆ T H := Finset.filter_subset _ _
  have he₁ := sum_error_le (F := F₁) (r := 1 / 2 + ε / 2) (c := 3) (by positivity) (by norm_num)
    h₁ hH1 (by nlinarith [sq_nonneg H]) (fun s => 3 * H ^ 2 + (s : ℝ) ^ 2)
    (fun s hs => ⟨by nlinarith [sq_nonneg (s : ℝ)], by nlinarith [sq_le_of_mem hs]⟩) T₁ hT₁
  have he₀ := sum_error_le (F := F₀) (r := 1 / 2 + ε / 2) (c := 1) (by positivity) (by norm_num)
    h₀ hH1 (by linarith) (fun s => H ^ 2 + (s : ℝ) ^ 2 / 3)
    (fun s hs => ⟨by nlinarith [sq_nonneg (s : ℝ)], by nlinarith [sq_le_of_mem hs]⟩) T₀ hT₀
  have hcard : (T₁.card : ℝ) + T₀.card ≤ 3 * H := by
    have := Finset.card_filter_add_card_filter_not (s := T H) (fun s => 3 ∣ s)
    have h' : ((T₀.card + T₁.card : ℕ) : ℝ) = (T H).card := by exact_mod_cast this
    push_cast at h'; linarith [card_T_le hH1]
  rw [four_sq_rpow hH0] at he₁ he₀
  set W := (4 : ℝ) ^ (1 / 2 + ε / 2) * H ^ (1 + ε)
  have hW : 0 ≤ W := by positivity
  have hHW : H * W = 4 ^ (1 / 2 + ε / 2) * H ^ (2 + ε) := by
    simp only [W]
    rw [mul_left_comm, ← Real.rpow_one_add' hH0.le (by linarith)]; ring_nf
  have hx : 0 ≤ |K₁| * W := mul_nonneg (abs_nonneg K₁) hW
  have hy : 0 ≤ |K₀| * W := mul_nonneg (abs_nonneg K₀) hW
  have hc1 : (0 : ℝ) ≤ T₁.card := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ T₀.card := Nat.cast_nonneg _
  have step : (T₁.card : ℝ) * (|K₁| * W) + T₀.card * (|K₀| * W) ≤
      ((T₁.card : ℝ) + T₀.card) * (|K₁| * W + |K₀| * W) := by
    have := mul_nonneg hc1 hy
    have := mul_nonneg hc0 hx
    linarith [show ((T₁.card : ℝ) + T₀.card) * (|K₁| * W + |K₀| * W) =
      T₁.card * (|K₁| * W) + T₀.card * (|K₀| * W) + (T₁.card * (|K₀| * W) +
        T₀.card * (|K₁| * W)) by ring]
  calc _ ≤ (T₁.card : ℝ) * (|K₁| * W) + T₀.card * (|K₀| * W) := add_le_add he₁ he₀
    _ ≤ ((T₁.card : ℝ) + T₀.card) * (|K₁| * W + |K₀| * W) := step
    _ ≤ 3 * H * (|K₁| * W + |K₀| * W) := mul_le_mul_of_nonneg_right hcard (add_nonneg hx hy)
    _ = 3 * ((|K₁| + |K₀|) * 4 ^ (1 / 2 + ε / 2)) * H ^ (2 + ε) := by
        rw [show 3 * H * (|K₁| * W + |K₀| * W) = 3 * (|K₁| + |K₀|) * (H * W) by ring, hHW]; ring

/-- The Riemann-sum remainder is `O(H² log H) ⊆ O(H^{2+ε})`. -/
theorem remainder_bound {a₁ b₁ a₀ b₀ D₁ D₂ E₁ E₂ H ε : ℝ} (hε : 0 < ε) (hH1 : 1 ≤ H)
    (bD₁ : |D₁| ≤ 52) (bD₂ : |D₂| ≤ 372) (bE₁ : |E₁| ≤ 26) (bE₂ : |E₂| ≤ 186) :
    |H ^ 2 * ((2 * a₁ * Real.log H + b₁) * D₁ + a₁ * D₂) +
        H ^ 2 / 3 * ((2 * a₀ * Real.log H - a₀ * Real.log 3 + b₀) * E₁ + a₀ * E₂)| ≤
      ((2 * |a₁| * 52 + 2 * |a₀| * 26 / 3) / ε +
        (|b₁| * 52 + |a₁| * 372 + (|a₀| * Real.log 3 + |b₀|) * 26 / 3 + |a₀| * 186 / 3)) *
        H ^ (2 + ε) := by
  set L := Real.log H
  have hH0 : 0 < H := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg hH1
  have ha₁ := abs_nonneg a₁
  have ha₀ := abs_nonneg a₀
  have hb₁ := abs_nonneg b₁
  have hb₀ := abs_nonneg b₀
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set cL := 2 * |a₁| * 52 + 2 * |a₀| * 26 / 3 with hcLdef
  set c0 := |b₁| * 52 + |a₁| * 372 + (|a₀| * Real.log 3 + |b₀|) * 26 / 3 + |a₀| * 186 / 3
    with hc0def
  have c1 : |2 * a₁ * L + b₁| ≤ 2 * |a₁| * L + |b₁| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hL0]; norm_num
  have c0' : |2 * a₀ * L - a₀ * Real.log 3 + b₀| ≤ 2 * |a₀| * L + |a₀| * Real.log 3 + |b₀| := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans ?_) le_rfl
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hL0, abs_of_nonneg hl3]; norm_num
  have r1 : |(2 * a₁ * L + b₁) * D₁ + a₁ * D₂| ≤ (2 * |a₁| * L + |b₁|) * 52 + |a₁| * 372 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_mul_le_of bD₂))
    exact (abs_mul_le_of bD₁).trans (mul_le_mul_of_nonneg_right c1 (by norm_num))
  have r0 : |(2 * a₀ * L - a₀ * Real.log 3 + b₀) * E₁ + a₀ * E₂| ≤
      (2 * |a₀| * L + |a₀| * Real.log 3 + |b₀|) * 26 + |a₀| * 186 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_mul_le_of bE₂))
    exact (abs_mul_le_of bE₁).trans (mul_le_mul_of_nonneg_right c0' (by norm_num))
  have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
  have hR : |H ^ 2 * ((2 * a₁ * L + b₁) * D₁ + a₁ * D₂) +
      H ^ 2 / 3 * ((2 * a₀ * L - a₀ * Real.log 3 + b₀) * E₁ + a₀ * E₂)| ≤
      H ^ 2 * (cL * L + c0) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hH2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ H ^ 2 / 3)]
    have := add_le_add (mul_le_mul_of_nonneg_left r1 hH2)
      (mul_le_mul_of_nonneg_left r0 (by positivity : (0 : ℝ) ≤ H ^ 2 / 3))
    refine this.trans (le_of_eq ?_)
    rw [hcLdef, hc0def]; ring
  have hLε : L ≤ H ^ ε / ε := Real.log_le_rpow_div hH0.le hε
  have hHε : 1 ≤ H ^ ε := Real.one_le_rpow hH1 hε.le
  have hsplit : H ^ (2 + ε) = H ^ 2 * H ^ ε := by
    rw [Real.rpow_add hH0, Real.rpow_two]
  have hcL : 0 ≤ cL := by positivity
  have hc0 : 0 ≤ c0 := by positivity
  refine hR.trans ?_
  rw [hsplit]
  have h1 : cL * L ≤ cL / ε * H ^ ε :=
    calc cL * L ≤ cL * (H ^ ε / ε) := mul_le_mul_of_nonneg_left hLε hcL
      _ = cL / ε * H ^ ε := by ring
  have h2 : c0 ≤ c0 * H ^ ε := le_mul_of_one_le_right hc0 hHε
  have : cL * L + c0 ≤ (cL / ε + c0) * H ^ ε := by
    linarith [show (cL / ε + c0) * H ^ ε = cL / ε * H ^ ε + c0 * H ^ ε by ring]
  calc H ^ 2 * (cL * L + c0) ≤ H ^ 2 * ((cL / ε + c0) * H ^ ε) :=
        mul_le_mul_of_nonneg_left this hH2
    _ = (cL / ε + c0) * (H ^ 2 * H ^ ε) := by ring

/-- The count with the trace-count coefficients. -/
theorem trace_count
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) (ε : ℝ) (hε : 0 < ε) :
    (fun H : ℝ => (Nat.card (generalSet H) : ℝ) -
      (Cmon * H ^ 3 * Real.log H + Dmon * H ^ 3)) =O[Filter.atTop] (fun H : ℝ => H ^ (2 + ε)) := by
  obtain ⟨-, hA1⟩ := Cubic.Counting.A1Asymptotic.coefficient_estimate hPoisson hCN
  obtain ⟨-, hA0⟩ := Cubic.Counting.TraceZeroAsymptotic.coefficient_estimate hPoisson hCN
  obtain ⟨K₁, X₁, h₁⟩ := hA1 (ε / 2) (by positivity)
  obtain ⟨K₀, X₀, h₀⟩ := hA0 (ε / 2) (by positivity)
  set a₁ := Cconst / 6 with ha₁def
  set b₁ := Dconst / 3 - Real.pi / (9 * √3) with hb₁def
  set a₀ := 5 * Cconst / 6 with ha₀def
  set b₀ := 5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3 - Real.pi / (3 * √3) with hb₀def
  set J := 40 / 3 * Real.log 2 + 4 * Real.pi * √3 / 3 - 76 / 9 with hJdef
  set cE := 3 * ((|K₁| + |K₀|) * 4 ^ (1 / 2 + ε / 2))
  set cL := 2 * |a₁| * 52 + 2 * |a₀| * 26 / 3 with hcLdef
  set c0 := |b₁| * 52 + |a₁| * 372 + (|a₀| * Real.log 3 + |b₀|) * 26 / 3 + |a₀| * 186 / 3 with hc0def
  refine Asymptotics.IsBigO.of_bound (cE + cL / ε + c0) ?_
  rw [Filter.eventually_atTop]
  refine ⟨max 3 (max (√|X₁|) (√|X₀|)), fun H hH => ?_⟩
  have hH3 : 3 ≤ H := le_trans (le_max_left _ _) hH
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hX₁ : X₁ ≤ H ^ 2 := le_trans (le_abs_self _)
    ((Real.sqrt_le_left hH0.le).mp (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hH)))
  have hX₀ : X₀ ≤ H ^ 2 := le_trans (le_abs_self _)
    ((Real.sqrt_le_left hH0.le).mp (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hH)))
  obtain ⟨-, hdec⟩ := Cubic.Counting.GeneralTraceDecomposition.«eqn:generalTraceDecomposition» H
  have hP : 0 < H ^ (2 + ε) := Real.rpow_pos_of_pos hH0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP, hdec]
  push_cast
  set L := Real.log H with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hH1
  set T₁ := (T H).filter (fun s => ¬ 3 ∣ s)
  set T₀ := (T H).filter (fun s => 3 ∣ s)
  -- main terms and errors
  set F₁ : ℝ → ℝ := fun X => (A₁ X : ℝ) - (a₁ * X * Real.log X + b₁ * X)
  set F₀ : ℝ → ℝ := fun X => (A₀ X : ℝ) - (a₀ * X * Real.log X + b₀ * X)
  have hsum₁ : ∑ s ∈ T₁, (A₁ (3 * H ^ 2 + (s : ℝ) ^ 2) : ℝ) =
      H ^ 2 * ((2 * a₁ * L + b₁) * ∑ s ∈ T₁, g₁ (s / H) + a₁ * ∑ s ∈ T₁, g₂ (s / H)) +
        ∑ s ∈ T₁, F₁ (3 * H ^ 2 + (s : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := main_one a₁ b₁ hH0 s
    rw [← hLdef] at this
    simp only [F₁]; rw [this]; ring
  have hsum₀ : ∑ s ∈ T₀, (A₀ (H ^ 2 + (s : ℝ) ^ 2 / 3) : ℝ) =
      H ^ 2 / 3 * ((2 * a₀ * L - a₀ * Real.log 3 + b₀) * ∑ s ∈ T₀, g₁ (s / H) +
        a₀ * ∑ s ∈ T₀, g₂ (s / H)) + ∑ s ∈ T₀, F₀ (H ^ 2 + (s : ℝ) ^ 2 / 3) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := main_zero a₀ b₀ hH0 s
    rw [← hLdef] at this
    simp only [F₀]; rw [this]; ring
  change |∑ s ∈ T₁, (A₁ (3 * H ^ 2 + (s : ℝ) ^ 2) : ℝ) +
    ∑ s ∈ T₀, (A₀ (H ^ 2 + (s : ℝ) ^ 2 / 3) : ℝ) - (Cmon * H ^ 3 * L + Dmon * H ^ 3)| ≤ _
  rw [hsum₁, hsum₀]
  -- errors of the expansions
  have hE := errors_bound (F₁ := F₁) (F₀ := F₀) hε hH1 h₁ h₀ hX₁ hX₀
  -- Riemann sums
  have hall₁ := riemann_all continuous_g₁ (by norm_num) lip_g₁ bound_g₁ hH1
  have hall₂ := riemann_all continuous_g₂ (by norm_num) lip_g₂ bound_g₂ hH1
  have hz₁ := riemann_zero continuous_g₁ (by norm_num) lip_g₁ bound_g₁ hH3
  have hz₂ := riemann_zero continuous_g₂ (by norm_num) lip_g₂ bound_g₂ hH3
  rw [integral_g₁] at hall₁ hz₁
  rw [integral_g₂] at hall₂ hz₂
  have hsp : ∀ g : ℝ → ℝ, ∑ s ∈ T₁, g (s / H) = ∑ s ∈ T H, g (s / H) - ∑ s ∈ T₀, g (s / H) :=
    fun g => by rw [← Finset.sum_filter_not_add_sum_filter (T H) (fun s => 3 ∣ s)]; ring
  rw [hsp g₁, hsp g₂]
  set D₁ := ∑ s ∈ T H, g₁ (s / H) - ∑ s ∈ T₀, g₁ (s / H) - 2 * H / 3 * (20 / 3) with eqD₁
  set D₂ := ∑ s ∈ T H, g₂ (s / H) - ∑ s ∈ T₀, g₂ (s / H) - 2 * H / 3 * J with eqD₂
  set E₁ := ∑ s ∈ T₀, g₁ (s / H) - H / 3 * (20 / 3) with hE₁def
  set E₂ := ∑ s ∈ T₀, g₂ (s / H) - H / 3 * J with hE₂def
  have bD₁ : |D₁| ≤ 52 := by
    have := abs_sub (∑ s ∈ T H, g₁ (s / H) - H * (20 / 3)) E₁
    rw [show D₁ = (∑ s ∈ T H, g₁ (s / H) - H * (20 / 3)) - E₁ by simp only [D₁, E₁]; ring]
    norm_num at hall₁ hz₁ ⊢; linarith
  have bD₂ : |D₂| ≤ 372 := by
    have := abs_sub (∑ s ∈ T H, g₂ (s / H) - H * J) E₂
    rw [show D₂ = (∑ s ∈ T H, g₂ (s / H) - H * J) - E₂ by simp only [D₂, E₂]; ring]
    norm_num at hall₂ hz₂ ⊢; linarith
  have bE₁ : |E₁| ≤ 26 := by norm_num at hz₁; exact hz₁
  have bE₂ : |E₂| ≤ 186 := by norm_num at hz₂; exact hz₂
  -- the remainder
  have hid := coefficients H L
  rw [← hJdef] at hid
  set R := H ^ 2 * ((2 * a₁ * L + b₁) * D₁ + a₁ * D₂) +
    H ^ 2 / 3 * ((2 * a₀ * L - a₀ * Real.log 3 + b₀) * E₁ + a₀ * E₂) with hRdef
  set G₁ := ∑ s ∈ T₁, F₁ (3 * H ^ 2 + (s : ℝ) ^ 2)
  set G₀ := ∑ s ∈ T₀, F₀ (H ^ 2 + (s : ℝ) ^ 2 / 3)
  have hkey : H ^ 2 * ((2 * a₁ * L + b₁) * (∑ s ∈ T H, g₁ (s / H) - ∑ s ∈ T₀, g₁ (s / H)) +
        a₁ * (∑ s ∈ T H, g₂ (s / H) - ∑ s ∈ T₀, g₂ (s / H))) + G₁ +
      (H ^ 2 / 3 * ((2 * a₀ * L - a₀ * Real.log 3 + b₀) * ∑ s ∈ T₀, g₁ (s / H) +
        a₀ * ∑ s ∈ T₀, g₂ (s / H)) + G₀) - (Cmon * H ^ 3 * L + Dmon * H ^ 3) = R + G₁ + G₀ := by
    rw [hRdef, eqD₁, eqD₂, hE₁def, hE₂def, ha₁def, hb₁def, ha₀def, hb₀def]
    linear_combination hid
  rw [hkey]
  have hR' : |R| ≤ (cL / ε + c0) * H ^ (2 + ε) := by
    rw [hRdef, hcLdef, hc0def]
    exact remainder_bound hε hH1 bD₁ bD₂ bE₁ bE₂
  calc |R + G₁ + G₀| ≤ |R| + (|G₁| + |G₀|) := by
        have := abs_add_le (R + G₁) G₀
        have := abs_add_le R G₁
        linarith
    _ ≤ (cL / ε + c0) * H ^ (2 + ε) + cE * H ^ (2 + ε) := add_le_add hR' hE
    _ = (cE + cL / ε + c0) * H ^ (2 + ε) := by ring

/-- The trace-count coefficient `D_mon` after `eqn:monicArchimedeanMoments`. -/
theorem Dmon_eq : (Dmon : ℂ) = traceCountSecondary := by
  simp only [traceCountSecondary, MonicArchimedeanMoments.value_one,
    MonicConstantsFromTraceCounts.derivative_one, MonicConstantsFromTraceCounts.pi_div_nine_sqrt,
    MonicConstantsFromTraceCounts.pi_div_three_sqrt, Dmon]
  push_cast
  ring

open Cubic.Counting.AsymptoticConstantsData Cubic.Counting.AsymptoticConstantsConvergence in
theorem «thm:generalMonicCount»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    GeneralMonicCountClaim := by
  obtain ⟨Z, γ, C, D, hZ, hK, -⟩ :=
    AsymptoticPolynomialCount.«thm:asymptoticPolynomialCount» hPoisson hCN
  obtain ⟨hL, hS⟩ := MonicConstantsFromTraceCounts.coefficient_identities
  have hCc : Cconst = C := hK.original_leading.symm
  -- `C = (1/3) ∏ (1 - 2/(p(p+1)))`
  have hCl : (Cconst : ℂ) = 1 / 3 * Cubic.PoissonSummation.LeadingTermsData.splitProductAtTwo := by
    rw [hCc, hK.simplified_leading, simplifiedLeading, ← simplified_product_cast]; push_cast; ring
  -- `D/C` in terms of `γ_E`
  have hDC : (Dconst : ℂ) / (Cconst : ℂ) = simplifiedSecondaryRatio γ := by
    rw [← hK.simplified_secondary, Dconst, ← Cconst, hCc, ← hK.original_secondary]
    have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hK.positive.ne'
    push_cast; field_simp
  have hlead : (Cmon : ℂ) = monicLeading := by
    simp only [Cmon, monicLeading]; push_cast; rw [hCl]; ring
  refine ⟨Z, γ, Cmon, Dmon, hZ, hlead, ?_,
    Cubic.Counting.GeneralTraceDecomposition.generalSet_finite, trace_count hPoisson hCN⟩
  rw [Dmon_eq, hS, hL, monicSecondary, ← hlead, hDC, simplifiedSecondaryRatio]
  simp only [Cmon, simplified_log_cast]
  push_cast
  ring

end Cubic.Counting.GeneralMonicCount
