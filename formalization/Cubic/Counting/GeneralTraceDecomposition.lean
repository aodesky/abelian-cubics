import Cubic.Counting.GeneralHeightReduction
import Cubic.Counting.A1Asymptotic
import Cubic.Counting.TraceZeroSplitting

/-!
# Proof of `eqn:generalTraceDecomposition`

`lemma:generalHeightReduction` gives `H_w(f) ≤ H ⟺ |s| ≤ H and n ≤ s² + 3H²`, and identifies,
for each trace `s` and invariant `n`, the polynomials of `F_mon` of trace `s` and invariant `n`
with the trace-one polynomials of toric-height square `n` (`3 ∤ s`) or with the trace-zero
polynomials `t³ - (n/3) t + c` (`3 ∣ s`). Hence the polynomials of trace `s` and height at
most `H` correspond to those counted by `A₁(3H² + s²)`, respectively `A₀(H² + s²/3)`.
-/

noncomputable section

namespace Cubic.Counting.GeneralTraceDecomposition

open Polynomial Cubic.Counting.GeneralMonicData Cubic.Counting.PolynomialCountData
open Cubic.Counting.GeneralHeightReduction CubicTargets.Counting.GeneralMonic

/-- The polynomials of `F_mon` of trace `s` and height at most `H`. -/
def fiber (H : ℝ) (s : ℤ) : Set ℤ[X] := {f | f ∈ generalSet H ∧ trace f = s}

theorem signTranslate_injective {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (m : ℤ) :
    Function.Injective (signTranslate ε m) :=
  Function.LeftInverse.injective (signTranslate_inv hε m)

/-- Traces not divisible by `3`. -/
theorem bijOn_one {H : ℝ} {s : ℤ} (hs : ¬ 3 ∣ s) (hsH : |(s : ℝ)| ≤ H) :
    ∃ ε m : ℤ, (ε = 1 ∨ ε = -1) ∧
      Set.BijOn (signTranslate ε m) (fiber H s) (traceOneSet (3 * H ^ 2 + s ^ 2)) := by
  obtain ⟨h0, h1, -⟩ := «lemma:generalHeightReduction»
  obtain ⟨ε, hε, hmod⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ε * s ≡ 1 [ZMOD 3] := by
    rcases (by omega : s % 3 = 1 ∨ s % 3 = 2) with h | h
    · exact ⟨1, Or.inl rfl, by simp [Int.ModEq, h]⟩
    · exact ⟨-1, Or.inr rfl, by simp only [Int.ModEq]; omega⟩
  refine ⟨ε, (ε * s - 1) / 3, hε, ?_, (signTranslate_injective hε _).injOn, ?_⟩
  · rintro f ⟨⟨hf, hH⟩, htr⟩
    have hA : f ∈ {f | f ∈ monicCyclic ∧ trace f = s ∧ invariant f = invariant f} :=
      ⟨hf, htr, rfl⟩
    obtain ⟨hg, hn⟩ := (h1 s (invariant f) ε hs hε hmod).mapsTo hA
    refine ⟨hg, ?_⟩
    rw [hn]
    have := ((h0 f hf).2 H).mp hH
    rw [htr] at this; linarith [this.2]
  · rintro g ⟨hg, hX⟩
    obtain ⟨f, ⟨hf, htr, hn⟩, rfl⟩ := (h1 s (1 - 3 * g.coeff 1) ε hs hε hmod).surjOn ⟨hg, rfl⟩
    refine ⟨f, ⟨⟨hf, ?_⟩, htr⟩, rfl⟩
    rw [(h0 f hf).2 H, htr, hn]
    exact ⟨hsH, by push_cast at hX ⊢; linarith⟩

/-- Traces divisible by `3`. -/
theorem bijOn_zero {H : ℝ} {s : ℤ} (hs : 3 ∣ s) (hsH : |(s : ℝ)| ≤ H) :
    Set.BijOn (signTranslate 1 (s / 3)) (fiber H s) (traceZeroSet (H ^ 2 + (s : ℝ) ^ 2 / 3)) := by
  obtain ⟨h0, -, h2⟩ := «lemma:generalHeightReduction»
  have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  refine ⟨?_, (signTranslate_injective hε _).injOn, ?_⟩
  · rintro f ⟨⟨hf, hH⟩, htr⟩
    have hA : f ∈ {f | f ∈ monicCyclic ∧ trace f = s ∧ invariant f = invariant f} :=
      ⟨hf, htr, rfl⟩
    obtain ⟨N, c, hnN, hg, hc⟩ := (h2 s (invariant f) hs).mapsTo hA
    have hpos := (h0 f hf).1
    have hle := (((h0 f hf).2 H).mp hH).2
    rw [htr, hnN] at hle
    refine ⟨N, c, hg, by omega, ?_, hg ▸ hc⟩
    push_cast at hle; linarith
  · rintro g ⟨N, c, rfl, hN1, hNY, hc⟩
    obtain ⟨f, ⟨hf, htr, hn⟩, hfg⟩ := (h2 s (3 * N) hs).surjOn ⟨N, c, rfl, rfl, hc⟩
    refine ⟨f, ⟨⟨hf, ?_⟩, htr⟩, hfg⟩
    rw [(h0 f hf).2 H, htr, hn]
    exact ⟨hsH, by push_cast; linarith⟩

theorem abs_le_of_mem {H : ℝ} {s : ℤ} (hs : s ∈ Finset.Icc (-⌊H⌋) ⌊H⌋) : |(s : ℝ)| ≤ H := by
  rw [Finset.mem_Icc] at hs
  have h1 : (s : ℝ) ≤ ⌊H⌋ := by exact_mod_cast hs.2
  have h2 : ((-⌊H⌋ : ℤ) : ℝ) ≤ s := by exact_mod_cast hs.1
  push_cast at h2
  rw [abs_le]; constructor <;> linarith [Int.floor_le H]

theorem trace_mem {H : ℝ} {f : ℤ[X]} (hf : f ∈ generalSet H) :
    trace f ∈ Finset.Icc (-⌊H⌋) ⌊H⌋ := by
  obtain ⟨h0, -, -⟩ := «lemma:generalHeightReduction»
  have h := (((h0 f hf.1).2 H).mp hf.2).1
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  exact ⟨by have := Int.le_floor.mpr (by push_cast; linarith : ((-trace f : ℤ) : ℝ) ≤ H); omega,
    Int.le_floor.mpr h.2⟩

theorem card_fiber_one {H : ℝ} {s : ℤ} (hs : ¬ 3 ∣ s) (hsH : |(s : ℝ)| ≤ H) :
    (fiber H s).Finite ∧ Nat.card (fiber H s) = A₁ (3 * H ^ 2 + s ^ 2) := by
  obtain ⟨ε, m, -, h⟩ := bijOn_one hs hsH
  refine ⟨Set.Finite.of_finite_image (h.image_eq ▸ A1Asymptotic.traceOneSet_finite _) h.injOn,
    Nat.card_congr h.equiv⟩

theorem card_fiber_zero {H : ℝ} {s : ℤ} (hs : 3 ∣ s) (hsH : |(s : ℝ)| ≤ H) :
    (fiber H s).Finite ∧ Nat.card (fiber H s) = A₀ (H ^ 2 + (s : ℝ) ^ 2 / 3) := by
  have h := bijOn_zero hs hsH
  refine ⟨Set.Finite.of_finite_image
    (h.image_eq ▸ TraceZeroSplitting.traceZeroSet_finite _) h.injOn, Nat.card_congr h.equiv⟩

theorem fiber_finite {H : ℝ} {s : ℤ} (hsH : |(s : ℝ)| ≤ H) : (fiber H s).Finite := by
  by_cases hs : 3 ∣ s
  · exact (card_fiber_zero hs hsH).1
  · exact (card_fiber_one hs hsH).1

theorem generalSet_finite (H : ℝ) : (generalSet H).Finite := by
  refine (Set.Finite.biUnion (Finset.Icc (-⌊H⌋) ⌊H⌋).finite_toSet
    (fun s hs => fiber_finite (abs_le_of_mem hs))).subset ?_
  intro f hf
  simp only [Set.mem_iUnion, Finset.mem_coe]
  exact ⟨trace f, trace_mem hf, hf, rfl⟩

theorem «eqn:generalTraceDecomposition» : GeneralTraceDecompositionClaim := by
  intro H
  classical
  have hfin := generalSet_finite H
  refine ⟨hfin, ?_⟩
  set T := Finset.Icc (-⌊H⌋) ⌊H⌋
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := trace) (t := T)
      (fun f hf => trace_mem ((Set.Finite.mem_toFinset hfin).mp hf))]
  have hfib : ∀ s ∈ T, (hfin.toFinset.filter (fun f => trace f = s)).card = Nat.card (fiber H s) := by
    intro s hs
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext f
    simp [fiber]
  rw [Finset.sum_congr rfl hfib, ← Finset.sum_filter_not_add_sum_filter _ (fun s => 3 ∣ s)]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_filter] at hs
    exact (card_fiber_one hs.2 (abs_le_of_mem hs.1)).2
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_filter] at hs
    exact (card_fiber_zero hs.2 (abs_le_of_mem hs.1)).2

end Cubic.Counting.GeneralTraceDecomposition
