import CubicTargets.Counting.TraceDistribution
import Cubic.Counting.GeneralMonicCount
import Cubic.Counting.IntervalRiemannSum

/-!
# Proof of `thm:traceDistribution`

Following the paper. Restricting `eqn:generalTraceDecomposition` to the traces
`s ≡ r (mod 3)` with `u₁H ≤ s ≤ u₂H` writes `N_r(H; u₁, u₂)` as a sum of `A₁(3H² + s²)`
(`r ≠ 0`) or of `A₀(H² + s²/3)` (`r = 0`) over these traces. Since `Q` is linear with leading
coefficient `2α/9`, `eqn:A1asymptotic` and `prop:traceZeroAsymptotic` give
`A₁(X) = (α/18) X log X + O(X)` and `A₀(X) = (5α/18) X log X + O(X)`. With `u = s/H`, each
trace contributes `(α/9)(3 + u²)H² log H + O(H²)` if `r ≠ 0` and
`(5α/27)(3 + u²)H² log H + O(H²)` if `r = 0`. There are `O(H)` traces, and the Riemann sum
over the progression `s ≡ r (mod 3)` in `[u₁H, u₂H]` is `(H/3)∫_{u₁}^{u₂}(3 + u²) du + O(1)`
uniformly in `r`, `u₁` and `u₂` (`IntervalRiemannSum.riemann_interval`). This proves the
asymptotic formula. Summing over the three residue classes with `u₁ = -1`, `u₂ = 1` gives
the total count with leading term `(20/3)(11α/81) H³ log H`; dividing gives the proportions
and the density.
-/

noncomputable section

namespace Cubic.Counting.TraceDistribution

open Polynomial Filter Asymptotics
open Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralMonicIntegrals
open Cubic.Counting.IntegralPointCountData Cubic.Counting.GeneralTraceDecomposition
open Cubic.Counting.GeneralMonicCount (T card_T_le)
open CubicTargets.Counting.GeneralMonic
open CubicTargets.Counting.TraceDistribution
open scoped Topology

/-! ### Restricting the trace decomposition -/

/-- The polynomials of `F_mon` of height at most `H` whose trace satisfies `P`, counted
trace by trace. -/
theorem card_decomp (P : ℤ → Prop) [DecidablePred P] (H : ℝ) :
    {f | f ∈ generalSet H ∧ P (trace f)}.Finite ∧
      Nat.card {f | f ∈ generalSet H ∧ P (trace f)} =
        ∑ s ∈ (T H).filter P, Nat.card (fiber H s) := by
  classical
  have hfin : {f | f ∈ generalSet H ∧ P (trace f)}.Finite :=
    (generalSet_finite H).subset fun f hf => hf.1
  refine ⟨hfin, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := trace) (t := (T H).filter P) (fun f hf => by
      have := (Set.Finite.mem_toFinset hfin).mp hf
      exact Finset.mem_filter.mpr ⟨trace_mem this.1, this.2⟩)]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hPs := (Finset.mem_filter.mp hs).2
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  congr 1
  ext f
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, fiber]
  constructor
  · rintro ⟨⟨hf, -⟩, rfl⟩; exact ⟨hf, rfl⟩
  · rintro ⟨hf, rfl⟩; exact ⟨⟨hf, hPs⟩, rfl⟩

/-! ### One trace -/

/-- The coefficient of `(3 + u²) H² log H` contributed by one trace `s`. -/
def κ (s : ℤ) : ℝ := if 3 ∣ s then 5 * alpha / 27 else alpha / 9

theorem alpha_pos : 0 < alpha := by
  have h : 0 < Cconst := Cubic.Counting.AsymptoticConstantsAssembly.constants.positive
  rw [Cubic.Counting.CountPolynomialNormalization.C_eq_alpha] at h
  linarith

/-- `Q` is linear with leading coefficient `2α/9`. -/
theorem Q_linear (x : ℝ) :
    Q EulerKroneckerCalculation.value x =
      2 * alpha / 9 * x + Q EulerKroneckerCalculation.value 0 := by
  simp only [Q]; ring

theorem split_bound {A M T R E₁ E₂ : ℝ} (h1 : |A - M| ≤ E₁) (hM : M - T = R) (h2 : |R| ≤ E₂) :
    |A - T| ≤ E₁ + E₂ := by
  rw [show A - T = (A - M) + R by rw [← hM]; ring]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Each trace contributes `κ_s (3 + u²) H² log H + O(H²)`, with `u = s/H`. -/
theorem fiber_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    ∃ E H₀ : ℝ, 0 ≤ E ∧ 3 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ s ∈ T H,
      |(Nat.card (fiber H s) : ℝ) - κ s * g₁ (s / H) * H ^ 2 * Real.log H| ≤ E * H ^ 2 := by
  obtain ⟨-, hA1⟩ := A1Asymptotic.«eqn:A1asymptotic» hPoisson hCN
  obtain ⟨-, hA0⟩ := TraceZeroAsymptotic.«prop:traceZeroAsymptotic» hPoisson hCN
  obtain ⟨K₁, X₁, h₁⟩ := hA1 (1 / 2) (by norm_num)
  obtain ⟨K₀, X₀, h₀⟩ := hA0 (1 / 2) (by norm_num)
  set q := Q EulerKroneckerCalculation.value 0
  set a₁ := alpha / 18 with ha₁
  set b₁ := q / 2 - Real.pi / (9 * √3) with hb₁
  set a₀ := 5 * alpha / 18 with ha₀
  set b₀ := 5 / 2 * q - (alpha / 4 * Real.log 3 + Real.pi / (3 * √3)) with hb₀
  set E₁ := 4 * |K₁| + (7 * |b₁| + 42 * |a₁|) with hE₁def
  set E₀ := 4 * |K₀| + (7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀|) with hE₀def
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hE₁ : 0 ≤ E₁ := by positivity
  have hE₀ : 0 ≤ E₀ := by positivity
  refine ⟨E₁ + E₀, max 3 (max (√|X₁|) (√|X₀|)), by positivity, le_max_left _ _,
    fun H hH s hs => ?_⟩
  have hH3 : 3 ≤ H := le_trans (le_max_left _ _) hH
  have hH0 : 0 < H := by linarith
  have hX₁ : X₁ ≤ H ^ 2 := le_trans (le_abs_self _)
    ((Real.sqrt_le_left hH0.le).mp (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hH)))
  have hX₀ : X₀ ≤ H ^ 2 := le_trans (le_abs_self _)
    ((Real.sqrt_le_left hH0.le).mp (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hH)))
  have hsH := abs_le_of_mem hs
  have hs2 : (s : ℝ) ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsH 2
  have hu : (s : ℝ) / H ∈ Set.Icc (-2 : ℝ) 2 := by
    rw [abs_le] at hsH
    constructor
    · rw [le_div_iff₀ hH0]; linarith
    · rw [div_le_iff₀ hH0]; linarith
  have hg1 := bound_g₁ _ hu
  have hg2 := bound_g₂ _ hu
  have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
  have hpos : (0 : ℝ) ≤ 1 / 2 + 1 / 2 := by norm_num
  by_cases h3 : 3 ∣ s
  · rw [(card_fiber_zero h3 hsH).2]
    simp only [κ, if_pos h3]
    have e := h₀ (H ^ 2 + (s : ℝ) ^ 2 / 3) (by linarith [sq_nonneg (s : ℝ)])
    beta_reduce at e
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] at e
    have hM : 5 / 2 * (H ^ 2 + (s : ℝ) ^ 2 / 3) *
          Q EulerKroneckerCalculation.value (1 / 2 * Real.log (H ^ 2 + (s : ℝ) ^ 2 / 3)) -
        (alpha / 4 * Real.log 3 + Real.pi / (3 * √3)) * (H ^ 2 + (s : ℝ) ^ 2 / 3) =
        a₀ * (H ^ 2 + (s : ℝ) ^ 2 / 3) * Real.log (H ^ 2 + (s : ℝ) ^ 2 / 3) +
          b₀ * (H ^ 2 + (s : ℝ) ^ 2 / 3) := by
      rw [Q_linear]; ring
    rw [hM, GeneralMonicCount.main_zero a₀ b₀ hH0 s] at e
    have e1 : |K₀ * (H ^ 2 + (s : ℝ) ^ 2 / 3)| ≤ 4 * |K₀| * H ^ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < H ^ 2 + (s : ℝ) ^ 2 / 3)]
      have := mul_le_mul_of_nonneg_left (show H ^ 2 + (s : ℝ) ^ 2 / 3 ≤ 4 * H ^ 2 by linarith)
        (abs_nonneg K₀)
      linarith
    have hR : |H ^ 2 / 3 * ((-(a₀ * Real.log 3) + b₀) * g₁ (s / H) + a₀ * g₂ (s / H))| ≤
        (7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀|) * H ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ H ^ 2 / 3)]
      have : |(-(a₀ * Real.log 3) + b₀) * g₁ (s / H) + a₀ * g₂ (s / H)| ≤
          7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, mul_comm]
          refine mul_le_mul hg1 ((abs_add_le _ _).trans ?_) (abs_nonneg _) (by norm_num)
          rw [abs_neg, abs_mul, abs_of_nonneg hl3]
        · rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hg2 (abs_nonneg _)
      have h0 : 0 ≤ 7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀| := by positivity
      calc H ^ 2 / 3 * _ ≤ H ^ 2 / 3 * (7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀|) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ _ := by
            have := mul_nonneg h0 hH2
            linarith
    have hb := split_bound (le_trans e (le_abs_self _))
      (show H ^ 2 / 3 * ((2 * a₀ * Real.log H - a₀ * Real.log 3 + b₀) * g₁ (s / H) +
          a₀ * g₂ (s / H)) - 5 * alpha / 27 * g₁ (s / H) * H ^ 2 * Real.log H =
        H ^ 2 / 3 * ((-(a₀ * Real.log 3) + b₀) * g₁ (s / H) + a₀ * g₂ (s / H)) by
          rw [ha₀]; ring) hR
    refine hb.trans ?_
    have hexp : (E₁ + E₀) * H ^ 2 = E₁ * H ^ 2 + 4 * |K₀| * H ^ 2 +
        (7 * (|a₀| * Real.log 3 + |b₀|) + 42 * |a₀|) * H ^ 2 := by rw [hE₀def]; ring
    rw [hexp]
    linarith [mul_nonneg hE₁ hH2]
  · rw [(card_fiber_one h3 hsH).2]
    simp only [κ, if_neg h3]
    have e := h₁ (3 * H ^ 2 + (s : ℝ) ^ 2) (by linarith [sq_nonneg (s : ℝ), sq_nonneg H])
    beta_reduce at e
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] at e
    have hM : 1 / 2 * (3 * H ^ 2 + (s : ℝ) ^ 2) *
          Q EulerKroneckerCalculation.value (1 / 2 * Real.log (3 * H ^ 2 + (s : ℝ) ^ 2)) -
        Real.pi / (9 * √3) * (3 * H ^ 2 + (s : ℝ) ^ 2) =
        a₁ * (3 * H ^ 2 + (s : ℝ) ^ 2) * Real.log (3 * H ^ 2 + (s : ℝ) ^ 2) +
          b₁ * (3 * H ^ 2 + (s : ℝ) ^ 2) := by
      rw [Q_linear]; ring
    rw [hM, GeneralMonicCount.main_one a₁ b₁ hH0 s] at e
    have e1 : |K₁ * (3 * H ^ 2 + (s : ℝ) ^ 2)| ≤ 4 * |K₁| * H ^ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 3 * H ^ 2 + (s : ℝ) ^ 2)]
      have := mul_le_mul_of_nonneg_left (show 3 * H ^ 2 + (s : ℝ) ^ 2 ≤ 4 * H ^ 2 by linarith)
        (abs_nonneg K₁)
      linarith
    have hR : |H ^ 2 * (b₁ * g₁ (s / H) + a₁ * g₂ (s / H))| ≤
        (7 * |b₁| + 42 * |a₁|) * H ^ 2 := by
      rw [abs_mul, abs_of_nonneg hH2]
      have : |b₁ * g₁ (s / H) + a₁ * g₂ (s / H)| ≤ 7 * |b₁| + 42 * |a₁| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hg1 (abs_nonneg _)
        · rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hg2 (abs_nonneg _)
      calc H ^ 2 * _ ≤ H ^ 2 * (7 * |b₁| + 42 * |a₁|) := mul_le_mul_of_nonneg_left this hH2
        _ = _ := by ring
    have hb := split_bound (le_trans e (le_abs_self _))
      (show H ^ 2 * ((2 * a₁ * Real.log H + b₁) * g₁ (s / H) + a₁ * g₂ (s / H)) -
          alpha / 9 * g₁ (s / H) * H ^ 2 * Real.log H =
        H ^ 2 * (b₁ * g₁ (s / H) + a₁ * g₂ (s / H)) by rw [ha₁]; ring) hR
    refine hb.trans ?_
    have hexp : (E₁ + E₀) * H ^ 2 = E₀ * H ^ 2 + 4 * |K₁| * H ^ 2 +
        (7 * |b₁| + 42 * |a₁|) * H ^ 2 := by rw [hE₁def]; ring
    rw [hexp]
    linarith [mul_nonneg hE₀ hH2]

/-! ### The Riemann sum over a residue class -/

/-- `Σ_{u₁H ≤ s ≤ u₂H, s ≡ r (3)} g(s/H) = (H/3) ∫_{u₁}^{u₂} g + O(1)`, uniformly. -/
theorem residue_riemann {g : ℝ → ℝ} {M B : ℝ} (hg : Continuous g) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2, |g x - g y| ≤ M * |x - y|)
    (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B) {H : ℝ} (hH : 3 ≤ H) (r : ℤ) {u₁ u₂ : ℝ}
    (h1 : -1 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1)
    [DecidablePred (fun s : ℤ => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂)] :
    |∑ s ∈ (T H).filter (fun s : ℤ => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂),
        g (s / H) - H / 3 * ∫ u in u₁..u₂, g u| ≤ 3 * M + 2 * B := by
  have hH0 : 0 < H := by linarith
  obtain ⟨m, hmdef⟩ : ∃ m : ℤ, m = ⌈u₁ * H⌉ := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℤ, F = ⌊u₂ * H⌋ := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℤ, s₀ = m + (r - m) % 3 := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ((F - s₀) / 3 + 1).toNat := ⟨_, rfl⟩
  have hm1 : u₁ * H ≤ m := hmdef ▸ Int.le_ceil _
  have hm2 : (m : ℝ) < u₁ * H + 1 := hmdef ▸ Int.ceil_lt_add_one _
  have hF1 : (F : ℝ) ≤ u₂ * H := hFdef ▸ Int.floor_le _
  have hF2 : u₂ * H < F + 1 := hFdef ▸ Int.lt_floor_add_one _
  have hmF : m ≤ F + 1 := by
    have h : (m : ℝ) < F + 2 := by nlinarith
    have : m < F + 2 := by exact_mod_cast h
    omega
  have hFH : F ≤ ⌊H⌋ := hFdef ▸ Int.floor_mono (by nlinarith)
  have hmH : -⌊H⌋ ≤ m := by
    rw [hmdef, ← Int.ceil_neg]; exact Int.ceil_mono (by nlinarith)
  -- membership in the summation range
  have hmem : ∀ s : ℤ, s ∈ (T H).filter
      (fun s : ℤ => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂) ↔
      (s % 3 = r % 3 ∧ m ≤ s ∧ s ≤ F) := by
    intro s
    rw [Finset.mem_filter, le_div_iff₀ hH0, div_le_iff₀ hH0, Int.ModEq, ← Int.ceil_le,
      ← Int.le_floor, ← hmdef, ← hFdef]
    simp only [T, Finset.mem_Icc]
    constructor
    · rintro ⟨-, h, h', h''⟩; exact ⟨h, h', h''⟩
    · rintro ⟨h, h', h''⟩; exact ⟨⟨by omega, by omega⟩, h, h', h''⟩
  have hn₀ : ((n : ℕ) : ℤ) = if F - s₀ + 3 < 0 then 0 else (F - s₀) / 3 + 1 := by
    rw [hndef]; split_ifs with h <;> omega
  have hs0a : m ≤ s₀ := by omega
  have hs0b : s₀ ≤ m + 2 := by omega
  have hn1 : F + 1 ≤ s₀ + 3 * (n : ℤ) := by rw [hn₀]; split_ifs <;> omega
  have hn2 : s₀ + 3 * (n : ℤ) ≤ F + 3 := by rw [hn₀]; split_ifs <;> omega
  -- reindex by `s = s₀ + 3j`
  have hsum : ∑ s ∈ (T H).filter
      (fun s : ℤ => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂), g (s / H) =
      ∑ j ∈ Finset.range n, g (s₀ / H + j * (3 / H)) := by
    symm
    refine Finset.sum_nbij' (fun j : ℕ => s₀ + 3 * (j : ℤ)) (fun s => ((s - s₀) / 3).toNat)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      beta_reduce
      rw [hmem]
      have : (j : ℤ) < n := by exact_mod_cast hj
      refine ⟨by omega, by omega, ?_⟩
      rw [hn₀] at this; split_ifs at this <;> omega
    · intro s hs
      rw [hmem] at hs
      rw [Finset.mem_range]
      have : (((s - s₀) / 3).toNat : ℤ) < n := by
        rw [hn₀]; split_ifs <;> omega
      exact_mod_cast this
    · intro j _
      beta_reduce
      omega
    · intro s hs
      rw [hmem] at hs
      beta_reduce
      omega
    · intro j _
      congr 1
      push_cast
      field_simp
  rw [hsum]
  have hδ0 : 0 < 3 / H := by positivity
  have hδ1 : 3 / H ≤ 1 := by rw [div_le_one hH0]; exact hH
  have hn1r : (F : ℝ) + 1 ≤ s₀ + 3 * n := by exact_mod_cast hn1
  have hn2r : (s₀ : ℝ) + 3 * n ≤ F + 3 := by exact_mod_cast hn2
  have hs0ar : (m : ℝ) ≤ s₀ := by exact_mod_cast hs0a
  have hs0br : (s₀ : ℝ) ≤ m + 2 := by exact_mod_cast hs0b
  have hx : s₀ / H + n * (3 / H) = (s₀ + 3 * n) / H := by field_simp
  have hR := Cubic.Counting.IntervalRiemannSum.riemann_interval hg hM0 hM hB hδ0 hδ1 n h1 h12 h2
    (x₀ := s₀ / H)
    (by rw [le_div_iff₀ hH0]; linarith)
    (by rw [show u₁ + 3 / H = (u₁ * H + 3) / H by field_simp,
      div_lt_div_iff_of_pos_right hH0]; linarith)
    (by rw [hx, lt_div_iff₀ hH0]; linarith)
    (by rw [hx, show u₂ + 3 / H = (u₂ * H + 3) / H by field_simp,
      div_le_div_iff_of_pos_right hH0]; linarith)
  have e : ∑ j ∈ Finset.range n, g (s₀ / H + j * (3 / H)) - H / 3 * ∫ u in u₁..u₂, g u =
      H / 3 * (3 / H * ∑ j ∈ Finset.range n, g (s₀ / H + j * (3 / H)) -
        ∫ u in u₁..u₂, g u) := by
    rw [mul_sub, ← mul_assoc, show H / 3 * (3 / H) = 1 by field_simp, one_mul]
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < H / 3)]
  calc H / 3 * _ ≤ H / 3 * ((3 * M + 2 * B) * (3 / H)) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = 3 * M + 2 * B := by field_simp

/-! ### The asymptotic formula -/

/-- `c_r` of the theorem (`CubicTargets.Counting.TraceDistribution.c`). -/
abbrev cc (r : ℤ) : ℝ := CubicTargets.Counting.TraceDistribution.c r

theorem κ_eq {r s : ℤ} (hr : r ∈ ({0, 1, 2} : Set ℤ)) (hs : s ≡ r [ZMOD 3]) :
    κ s = 3 * cc r := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  simp only [Int.ModEq] at hs
  simp only [κ, cc, CubicTargets.Counting.TraceDistribution.c]
  rcases hr with rfl | rfl | rfl
  · rw [if_pos (by omega), if_pos rfl]; ring
  · rw [if_neg (by omega), if_neg (by norm_num)]; ring
  · rw [if_neg (by omega), if_neg (by norm_num)]; ring

theorem abs_c_le (r : ℤ) : |3 * cc r| ≤ alpha := by
  have ha := alpha_pos
  simp only [cc, CubicTargets.Counting.TraceDistribution.c]
  split_ifs
  · rw [abs_of_pos (by positivity)]; linarith
  · rw [abs_of_pos (by positivity)]; linarith

theorem estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    ∃ K H₀ : ℝ, 3 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ r ∈ ({0, 1, 2} : Set ℤ), ∀ u₁ u₂ : ℝ,
      -1 ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ 1 →
        |(N r H u₁ u₂ : ℝ) - cc r * (∫ u in u₁..u₂, (3 + u ^ 2)) * H ^ 3 * Real.log H| ≤
          K * H ^ 3 := by
  classical
  obtain ⟨E, H₀, hE, hH₀, hfib⟩ := fiber_estimate hPoisson hCN
  refine ⟨3 * E + 26 * alpha, H₀, hH₀, fun H hH r hr u₁ u₂ h1 h12 h2 => ?_⟩
  have hH3 : 3 ≤ H := le_trans hH₀ hH
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  set P : ℤ → Prop := fun s => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂
  set S := (T H).filter P with hS
  have hN : (N r H u₁ u₂ : ℝ) = ∑ s ∈ S, (Nat.card (fiber H s) : ℝ) := by
    rw [N, show traceSet r H u₁ u₂ = {f | f ∈ generalSet H ∧ P (trace f)} from rfl,
      (card_decomp P H).2]
    push_cast; rfl
  have hint : (∫ u in u₁..u₂, (3 + u ^ 2)) = ∫ u in u₁..u₂, g₁ u := rfl
  set L := Real.log H with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hH1
  have hLH : L ≤ H := (Real.log_le_sub_one_of_pos hH0).trans (by linarith)
  set I := ∫ u in u₁..u₂, g₁ u
  have hRiem := residue_riemann continuous_g₁ (by norm_num) lip_g₁ bound_g₁ hH3 r h1 h12 h2
  rw [← hS] at hRiem
  norm_num at hRiem
  have hκ : ∀ s ∈ S, κ s = 3 * cc r := fun s hs => κ_eq hr (Finset.mem_filter.mp hs).2.1
  have hsplit : (N r H u₁ u₂ : ℝ) - cc r * I * H ^ 3 * L =
      ∑ s ∈ S, ((Nat.card (fiber H s) : ℝ) - κ s * g₁ (s / H) * H ^ 2 * L) +
        3 * cc r * H ^ 2 * L * (∑ s ∈ S, g₁ (s / H) - H / 3 * I) := by
    have h3 : ∑ s ∈ S, κ s * g₁ (s / H) * H ^ 2 * L =
        3 * cc r * H ^ 2 * L * ∑ s ∈ S, g₁ (s / H) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s hs => by rw [hκ s hs]; ring
    rw [hN, Finset.sum_sub_distrib, h3]
    ring
  rw [hint, hsplit]
  have hcard : (S.card : ℝ) ≤ 3 * H :=
    (by exact_mod_cast Finset.card_filter_le _ _ : (S.card : ℝ) ≤ (T H).card).trans (card_T_le hH1)
  have hfirst : |∑ s ∈ S, ((Nat.card (fiber H s) : ℝ) - κ s * g₁ (s / H) * H ^ 2 * L)| ≤
      3 * E * H ^ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun s hs => hfib H hH s (Finset.mem_of_mem_filter s hs)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (S.card : ℝ) * (E * H ^ 2) ≤ 3 * H * (E * H ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    nlinarith
  have hsecond : |3 * cc r * H ^ 2 * L * (∑ s ∈ S, g₁ (s / H) - H / 3 * I)| ≤
      26 * alpha * H ^ 3 := by
    rw [abs_mul, show 3 * cc r * H ^ 2 * L = (3 * cc r) * (H ^ 2 * L) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ H ^ 2 * L)]
    have hc := abs_c_le r
    have hα := alpha_pos
    have h1' : H ^ 2 * L ≤ H ^ 3 := by nlinarith [sq_nonneg H]
    have h2' : |3 * cc r| * (H ^ 2 * L) ≤ alpha * H ^ 3 :=
      mul_le_mul hc h1' (by positivity) hα.le
    calc |3 * cc r| * (H ^ 2 * L) * |∑ s ∈ S, g₁ (s / H) - H / 3 * I|
        ≤ alpha * H ^ 3 * 26 :=
          mul_le_mul h2' hRiem (abs_nonneg _) (by positivity)
      _ = 26 * alpha * H ^ 3 := by ring
  calc _ ≤ 3 * E * H ^ 3 + 26 * alpha * H ^ 3 := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    _ = (3 * E + 26 * alpha) * H ^ 3 := by ring

/-! ### The total over the residue classes -/

theorem total (H : ℝ) (hH : 0 < H) :
    Nat.card (generalSet H) = N 0 H (-1) 1 + N 1 H (-1) 1 + N 2 H (-1) 1 := by
  classical
  have hall := (card_decomp (fun _ => True) H).2
  have hset : {f | f ∈ generalSet H ∧ True} = generalSet H := by ext f; simp
  rw [hset, Finset.filter_true_of_mem (fun _ _ => trivial)] at hall
  have hr : ∀ r : ℤ, N r H (-1) 1 = ∑ s ∈ (T H).filter
      (fun s : ℤ => s ≡ r [ZMOD 3] ∧ -1 ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ 1),
        Nat.card (fiber H s) := fun r =>
    (card_decomp (fun s : ℤ => s ≡ r [ZMOD 3] ∧ -1 ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ 1) H).2
  rw [hall, hr 0, hr 1, hr 2, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsH := abs_le_of_mem hs
  rw [abs_le] at hsH
  have hb1 : -1 ≤ (s : ℝ) / H := by rw [le_div_iff₀ hH]; linarith
  have hb2 : (s : ℝ) / H ≤ 1 := by rw [div_le_iff₀ hH]; linarith
  simp only [Int.ModEq, hb1, hb2, and_true]
  rcases (by omega : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2) with h | h | h <;> simp [h]

/-! ### Ratios -/

theorem tendsto_normalized {F : ℝ → ℝ} {a K H₀ : ℝ}
    (h : ∀ H, H₀ ≤ H → |F H - a * H ^ 3 * Real.log H| ≤ K * H ^ 3) :
    Tendsto (fun H => F H / (H ^ 3 * Real.log H)) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun H : ℝ => |K| / Real.log H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  rw [eventually_atTop]
  refine ⟨max H₀ 2, fun H hH => ?_⟩
  have hH2 : 2 ≤ H := le_trans (le_max_right _ _) hH
  have hL : 0 < Real.log H := Real.log_pos (by linarith)
  have hH3 : 0 < H ^ 3 := by positivity
  have hb := h H (le_trans (le_max_left _ _) hH)
  rw [Real.norm_eq_abs, show F H / (H ^ 3 * Real.log H) - a =
    (F H - a * H ^ 3 * Real.log H) / (H ^ 3 * Real.log H) by field_simp, abs_div,
    abs_of_pos (by positivity : 0 < H ^ 3 * Real.log H), div_le_div_iff₀ (by positivity) hL]
  calc |F H - a * H ^ 3 * Real.log H| * Real.log H ≤ K * H ^ 3 * Real.log H :=
        mul_le_mul_of_nonneg_right hb hL.le
    _ ≤ |K| * (H ^ 3 * Real.log H) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hH3.le)
          hL.le

theorem tendsto_ratio {F G : ℝ → ℝ} {a b K₁ K₂ H₁ H₂ : ℝ} (hb : b ≠ 0)
    (hF : ∀ H, H₁ ≤ H → |F H - a * H ^ 3 * Real.log H| ≤ K₁ * H ^ 3)
    (hG : ∀ H, H₂ ≤ H → |G H - b * H ^ 3 * Real.log H| ≤ K₂ * H ^ 3) :
    Tendsto (fun H => F H / G H) atTop (𝓝 (a / b)) := by
  refine ((tendsto_normalized hF).div (tendsto_normalized hG) hb).congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨2, fun H hH => ?_⟩
  have : H ^ 3 * Real.log H ≠ 0 := (mul_pos (by positivity) (Real.log_pos (by linarith))).ne'
  exact div_div_div_cancel_right₀ this _ _

theorem «thm:traceDistribution»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.TraceDistribution.Claim := by
  classical
  obtain ⟨K, H₀, hH₀, hest⟩ := estimate hPoisson hCN
  have hα := alpha_pos
  have hI : (∫ u in (-1 : ℝ)..1, (3 + u ^ 2)) = 20 / 3 := integral_g₁
  have hfull : ∀ r ∈ ({0, 1, 2} : Set ℤ), ∀ H, H₀ ≤ H →
      |(N r H (-1) 1 : ℝ) - cc r * (20 / 3) * H ^ 3 * Real.log H| ≤ K * H ^ 3 :=
    fun r hr H hH => by
      have := hest H hH r hr (-1) 1 le_rfl (by norm_num) le_rfl
      rwa [hI] at this
  have h0 : (0 : ℤ) ∈ ({0, 1, 2} : Set ℤ) := by simp
  have h1 : (1 : ℤ) ∈ ({0, 1, 2} : Set ℤ) := by simp
  have h2 : (2 : ℤ) ∈ ({0, 1, 2} : Set ℤ) := by simp
  have hc0 : cc 0 = 5 * alpha / 81 := by simp [cc, CubicTargets.Counting.TraceDistribution.c]
  have hc1 : cc 1 = alpha / 27 := by simp [cc, CubicTargets.Counting.TraceDistribution.c]
  have hc2 : cc 2 = alpha / 27 := by simp [cc, CubicTargets.Counting.TraceDistribution.c]
  -- the total count
  have htot : ∀ H, max H₀ 1 ≤ H →
      |(Nat.card (generalSet H) : ℝ) - (cc 0 + cc 1 + cc 2) * (20 / 3) * H ^ 3 * Real.log H| ≤
        (3 * K) * H ^ 3 := by
    intro H hH
    have hH' : H₀ ≤ H := le_trans (le_max_left _ _) hH
    have hpos : 0 < H := by linarith [le_trans (le_max_right _ _) hH]
    rw [total H hpos]
    push_cast
    have e0 := hfull 0 h0 H hH'
    have e1 := hfull 1 h1 H hH'
    have e2 := hfull 2 h2 H hH'
    rw [abs_le] at e0 e1 e2 ⊢
    constructor <;> nlinarith
  have hb : (cc 0 + cc 1 + cc 2) * (20 / 3) ≠ 0 := by
    rw [hc0, hc1, hc2]; positivity
  have hprop : ∀ r ∈ ({0, 1, 2} : Set ℤ),
      Tendsto (fun H => (N r H (-1) 1 : ℝ) / Nat.card (generalSet H)) atTop
        (𝓝 (cc r * (20 / 3) / ((cc 0 + cc 1 + cc 2) * (20 / 3)))) :=
    fun r hr => tendsto_ratio hb (hfull r hr) htot
  refine ⟨fun r H u₁ u₂ =>
    (card_decomp (fun s : ℤ => s ≡ r [ZMOD 3] ∧ u₁ ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ u₂) H).1,
    ⟨K, H₀, hest⟩, ?_, ?_, ?_, ?_⟩
  · convert hprop 0 h0 using 2
    rw [hc0, hc1, hc2]; field_simp; ring
  · convert hprop 1 h1 using 2
    rw [hc0, hc1, hc2]; field_simp; ring
  · convert hprop 2 h2 using 2
    rw [hc0, hc1, hc2]; field_simp; ring
  · intro r hr u₁ u₂ hu₁ hu₁₂ hu₂
    have hcr : cc r ≠ 0 := by
      simp only [cc, CubicTargets.Counting.TraceDistribution.c]; split_ifs <;> positivity
    have hlim := tendsto_ratio (by positivity : cc r * (20 / 3) ≠ 0)
      (fun H hH => hest H hH r hr u₁ u₂ hu₁ hu₁₂ hu₂) (hfull r hr)
    convert hlim using 2
    rw [intervalIntegral.integral_const_mul]
    field_simp

end Cubic.Counting.TraceDistribution
