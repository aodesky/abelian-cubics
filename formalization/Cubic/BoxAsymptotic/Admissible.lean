import Cubic.BoxAsymptotic.LatticeCount
import Cubic.BoxAsymptotic.TraceClass
import Cubic.BoxAsymptotic.SplitCount

/-!
# Admissible pairs grouped by `β` (`eq:continuous`, first half)

The admissible `(s, n, A, B)` of `Parametrization.pairs` are grouped by `β = A + Bζ`: for
each admissible `β` of norm `n³` the allowed `s` are the integers of the residue class of
`TraceClass.cong_iff` in the trace set `E(H, n, arg β)`, because
`2A - B = 2 Re β = 2 n^{3/2} cos(arg β)`. All `β` have `n ≤ H² + 3H`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Admissible

open CubicTargets.BoxAsymptotic (eis admissible)
open Cubic.BoxAsymptotic.EisensteinCoordinates (nrm norm_eis_sq)
open Cubic.BoxAsymptotic.TraceWidth Cubic.BoxAsymptotic.LatticeCount

/-- `2 n^{3/2} cos(arg β) = 2A - B` for `N β = n³`. -/
theorem two_re {β : ℤ × ℤ} {n : ℕ} (h : nrm β = (n : ℤ) ^ 3) :
    2 * ((n : ℝ) * Real.sqrt n) * Real.cos (Complex.arg (eis β)) = 2 * β.1 - β.2 := by
  have hn : ‖eis β‖ = (n : ℝ) * Real.sqrt n := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_eis_sq, h]
    push_cast
    rw [show ((n : ℝ) ^ 3) = (n : ℝ) ^ 2 * n by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [← hn, mul_assoc, Complex.norm_mul_cos_arg]
  simp only [eis]; ring

/-- The bound `n ≤ N(H) = ⌊H² + 3H⌋₊`. -/
def Nmax (H : ℝ) : ℕ := ⌊H ^ 2 + 3 * H⌋₊

/-- A box for `(A, B)`. -/
def box (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(2 * (N : ℤ) ^ 3)) (2 * (N : ℤ) ^ 3) ×ˢ
    Finset.Icc (-(2 * (N : ℤ) ^ 3)) (2 * (N : ℤ) ^ 3)

open scoped Classical in
/-- All admissible `(n, β)` with `1 ≤ n ≤ N(H)`. -/
def Bset (H : ℝ) : Finset (ℕ × (ℤ × ℤ)) :=
  (Finset.Icc 1 (Nmax H) ×ˢ box (Nmax H)).filter fun x => x.2 ∈ admissible x.1

theorem mem_Bset {H : ℝ} {n : ℕ} {β : ℤ × ℤ} :
    (n, β) ∈ Bset H ↔ 1 ≤ n ∧ n ≤ Nmax H ∧ β ∈ admissible n := by
  classical
  rw [Bset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h⟩; exact ⟨h1, h2, h⟩
  · rintro ⟨h1, h2, h⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, h⟩
    have hN : nrm β = (n : ℤ) ^ 3 := h.1
    have hb1 := Cubic.BoxAsymptotic.LatticeSums.abs_le_nrm β.1 β.2
    have hb2 := Cubic.BoxAsymptotic.LatticeSums.abs_le_nrm β.2 β.1
    rw [Cubic.BoxAsymptotic.LatticeSums.nrm_swap] at hb2
    have hn3 : (n : ℤ) ^ 3 ≤ (Nmax H : ℤ) ^ 3 := by
      have : (n : ℤ) ≤ Nmax H := by exact_mod_cast h2
      exact pow_le_pow_left₀ (by positivity) this 3
    simp only [Prod.mk.eta] at hb1 hb2
    rw [hN] at hb1 hb2
    rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      [linarith [neg_abs_le β.1]; linarith [le_abs_self β.1];
        linarith [neg_abs_le β.2]; linarith [le_abs_self β.2]]

/-- The chosen admissible trace residue. -/
def s₀ (n : ℕ) (β : ℤ × ℤ) : ℤ :=
  open scoped Classical in
  if h : ∃ s : ℤ, s ^ 2 ≡ (n : ℤ) [ZMOD 3] ∧ 2 * β.1 - β.2 ≡ 3 * s * n - s ^ 3 [ZMOD 27]
  then h.choose else 0

theorem s₀_spec {n : ℕ} {β : ℤ × ℤ} (h : β ∈ admissible n) :
    s₀ n β ^ 2 ≡ (n : ℤ) [ZMOD 3] ∧ 2 * β.1 - β.2 ≡ 3 * s₀ n β * n - s₀ n β ^ 3 [ZMOD 27] := by
  classical
  have h' := h.2.2
  rw [s₀, dif_pos h']
  exact h'.choose_spec

/-- The argument of `β`. -/
def θ (β : ℤ × ℤ) : ℝ := Complex.arg (eis β)


open Cubic.BoxAsymptotic.Parametrization (pairs)

/-- Membership in `pairs` for an admissible `β`. -/
theorem mem_pairs_iff {H : ℝ} {s : ℤ} {n : ℕ} {β : ℤ × ℤ} (hn : 1 ≤ n)
    (hβ : β ∈ admissible n) :
    (s, (n : ℤ), β.1, β.2) ∈ pairs H ↔ β.2 ≠ 0 ∧ s ∈ traceSet H n (θ β) (s₀ n β) := by
  classical
  have hcong := TraceClass.cong_iff (s := s) (s₀_spec hβ).1 (s₀_spec hβ).2
  have hre := two_re (n := n) hβ.1
  simp only [pairs, Set.mem_setOf_eq, traceSet, Finset.mem_filter, Finset.mem_Icc, E, Q, θ]
  rw [← hcong, hre]
  constructor
  · rintro ⟨-, -, -, hB, hc1, hc2, h1, h2, h3⟩
    refine ⟨hB, ⟨?_, ?_⟩, ⟨hc1, hc2⟩, h1, ?_, ?_⟩
    · have : -(⌈H⌉ : ℝ) ≤ s := by
        have := neg_abs_le (s : ℝ); linarith [Int.le_ceil H]
      exact_mod_cast this
    · have : (s : ℝ) ≤ ⌈H⌉ := by
        have := le_abs_self (s : ℝ); linarith [Int.le_ceil H]
      exact_mod_cast this
    · push_cast at h2 ⊢; exact h2
    · push_cast at h3 ⊢; exact h3
  · rintro ⟨hB, -, ⟨hc1, hc2⟩, h1, h2, h3⟩
    refine ⟨by exact_mod_cast hn, hβ.1, hβ.2.1, hB, hc1, hc2, h1, ?_, ?_⟩
    · push_cast at h2 ⊢; exact h2
    · push_cast at h3 ⊢; exact h3


open scoped Classical in
/-- **Grouping by `β`**: `#pairs(H) = Σ_{β, B ≠ 0} #{s ≡ s₀(β) (mod 3) : s ∈ E(H, n, arg β)}`. -/
theorem card_pairs_sum (H : ℝ) :
    Nat.card (pairs H) = ∑ x ∈ (Bset H).filter (fun x => x.2.2 ≠ 0),
      (traceSet H x.1 (θ x.2) (s₀ x.1 x.2)).card := by
  set F := (Bset H).filter (fun x => x.2.2 ≠ 0)
  set emb : ℕ × (ℤ × ℤ) → ℤ → ℤ × ℤ × ℤ × ℤ := fun x s => (s, (x.1 : ℤ), x.2.1, x.2.2)
  set PF := F.biUnion fun x => (traceSet H x.1 (θ x.2) (s₀ x.1 x.2)).image (emb x)
  have hPF : pairs H = ↑PF := by
    ext y
    obtain ⟨s, m, A, B⟩ := y
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe, PF, emb, F, Finset.mem_filter]
    constructor
    · intro hy
      have hm : 0 < m := hy.1
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
      have hn1 : 1 ≤ n := by omega
      have hβ : (A, B) ∈ admissible n := ⟨hy.2.1, hy.2.2.1, s, hy.2.2.2.2.1, hy.2.2.2.2.2.1⟩
      have hnN : n ≤ Nmax H := by
        apply Nat.le_floor
        have h1 := hy.2.2.2.2.2.2.1
        have h2 := hy.2.2.2.2.2.2.2.1
        push_cast at h1 h2
        have hs2 : (s : ℝ) ^ 2 ≤ H ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have := (abs_le.mp h2).1
        linarith
      have hmem := (mem_pairs_iff (s := s) (H := H) hn1 hβ).mp hy
      exact ⟨(n, (A, B)), ⟨mem_Bset.mpr ⟨hn1, hnN, hβ⟩, hmem.1⟩, s, hmem.2, rfl⟩
    · rintro ⟨x, ⟨hx, hB⟩, s', hs', he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨hn1, -, hβ⟩ := mem_Bset.mp hx
      exact (mem_pairs_iff (s := s') hn1 hβ).mpr ⟨hB, hs'⟩
  rw [hPF, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun x _ => Finset.card_image_of_injective _ ?_
    intro a b h; simpa [emb] using h
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_image, emb] at ht ht'
    obtain ⟨a, -, rfl⟩ := ht
    obtain ⟨b, -, hb⟩ := ht'
    simp only [Prod.mk.injEq, Nat.cast_inj] at hb
    exact hxy (Prod.ext hb.2.1.symm (Prod.ext hb.2.2.1.symm hb.2.2.2.symm))

end Cubic.BoxAsymptotic.Admissible
