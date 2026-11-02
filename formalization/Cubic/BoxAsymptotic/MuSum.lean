import Cubic.BoxAsymptotic.Bands
import Cubic.BoxAsymptotic.PartitionIntegrals

/-!
# Sums over admissible pairs as `μ_n`-integrals

`Σ_{(n, β)} f(n, arg β) = 6 Σ_{1 ≤ n ≤ N(H)} ∫ f(n, ·) dμ_n`, and a weight supported on
`X/2 ≤ n ≤ 2X ≤ N(H)` has the same `μ`-sum over `n ≤ 4X` as over `1 ≤ n ≤ N(H)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.MuSum

open CubicTargets.BoxAsymptotic (eis admissible muIntegral)
open Cubic.BoxAsymptotic.Admissible
open scoped Classical

theorem admissible_finite (n : ℕ) : (admissible n).Finite := by
  refine (Finset.finite_toSet (box n)).subset fun β hβ => ?_
  have hb1 := Cubic.BoxAsymptotic.LatticeSums.abs_le_nrm β.1 β.2
  have hb2 := Cubic.BoxAsymptotic.LatticeSums.abs_le_nrm β.2 β.1
  rw [Cubic.BoxAsymptotic.LatticeSums.nrm_swap] at hb2
  have hN : Cubic.BoxAsymptotic.EisensteinCoordinates.nrm β = (n : ℤ) ^ 3 := hβ.1
  simp only [Prod.mk.eta] at hb1 hb2
  rw [hN] at hb1 hb2
  rw [Finset.mem_coe, box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    [linarith [neg_abs_le β.1]; linarith [le_abs_self β.1];
      linarith [neg_abs_le β.2]; linarith [le_abs_self β.2]]

theorem muIntegral_eq (n : ℕ) (g : ℝ → ℝ) :
    muIntegral n g = (1 / 6) * ∑ β ∈ (admissible_finite n).toFinset, g (θ β) := by
  rw [muIntegral, finsum_mem_eq_finite_toFinset_sum _ (admissible_finite n)]; rfl

/-- `Σ_{(n, β) ∈ Bset} f(n, arg β) = 6 Σ_{1 ≤ n ≤ N} ∫ f(n, ·) dμ_n`. -/
theorem sum_Bset (H : ℝ) (f : ℕ → ℝ → ℝ) :
    ∑ x ∈ Bset H, f x.1 (θ x.2) = 6 * ∑ n ∈ Finset.Icc 1 (Nmax H), muIntegral n (f n) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.Icc 1 (Nmax H))
    (fun x hx => by
      obtain ⟨h1, h2, -⟩ := mem_Bset.mp (by simpa using hx : (x.1, x.2) ∈ Bset H)
      exact Finset.mem_Icc.mpr ⟨h1, h2⟩)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [muIntegral_eq, ← mul_assoc, show (6 : ℝ) * (1 / 6) = 1 by norm_num, one_mul]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  refine Finset.sum_nbij' (fun x => x.2) (fun β => (n, β)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hB, rfl⟩ := hx
    have := (mem_Bset.mp (by simpa using hB : (x.1, x.2) ∈ Bset H)).2.2
    simpa using this
  · intro β hβ
    rw [Finset.mem_filter]
    exact ⟨mem_Bset.mpr ⟨h1, h2, by simpa using hβ⟩, rfl⟩
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, rfl⟩ := hx
    rfl
  · intro β _; rfl
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, rfl⟩ := hx
    rfl

/-- A weight supported on `X/2 ≤ n ≤ 2X` has the same `μ`-sum over `n ≤ 4X` and over
`1 ≤ n ≤ N`, when `2X ≤ N`. -/
theorem sum_range_eq {X : ℝ} {N : ℕ} (hX : 1 ≤ X) (hXN : 2 * X ≤ N) (w : ℕ → ℝ → ℝ)
    (hw : ∀ n : ℕ, ∀ θ, w n θ ≠ 0 → X / 2 ≤ n ∧ (n : ℝ) ≤ 2 * X) :
    ∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (w n) =
      ∑ n ∈ Finset.Icc 1 N, muIntegral n (w n) := by
  have hz : ∀ n : ℕ, ¬ (X / 2 ≤ n ∧ (n : ℝ) ≤ 2 * X) → muIntegral n (w n) = 0 := by
    intro n hn
    rw [muIntegral_eq]
    simp only [mul_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Finset.sum_eq_zero fun β _ => by
      by_contra h; exact hn (hw n _ h)
  set S := (Finset.range (⌊4 * X⌋₊ + 1)).filter fun n : ℕ => X / 2 ≤ n ∧ (n : ℝ) ≤ 2 * X
  have h1 : ∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (w n) =
      ∑ n ∈ S, muIntegral n (w n) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by split_ifs with h <;> [rfl; exact hz n h]
  have h2 : ∑ n ∈ Finset.Icc 1 N, muIntegral n (w n) = ∑ n ∈ S, muIntegral n (w n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
      (fun n : ℕ => X / 2 ≤ n ∧ (n : ℝ) ≤ 2 * X)]
    rw [Finset.sum_eq_zero (s := (Finset.Icc 1 N).filter fun n : ℕ => ¬ (X / 2 ≤ n ∧ (n : ℝ) ≤ 2 * X))
      fun n hn => hz n (Finset.mem_filter.mp hn).2, add_zero]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, S]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith [h.2])), h⟩
    · rintro ⟨-, h⟩
      refine ⟨⟨?_, ?_⟩, h⟩
      · have : (1 : ℝ) / 2 ≤ n := by linarith [h.1]
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this
      · exact_mod_cast h.2.trans hXN
  rw [h1, h2]

end Cubic.BoxAsymptotic.MuSum
