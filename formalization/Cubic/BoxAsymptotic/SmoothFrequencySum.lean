import Cubic.BoxAsymptotic.AngularMomentSums
import Cubic.BoxAsymptotic.SmoothDyadicKernel
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Exhausting the integer frequencies by the small modes and the disjoint
ranges `(2^(r+1),2^(r+2)]` in absolute value. This connects the dyadic moment
bounds to the full Fourier sum without assuming any omitted frequency vanishes. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothFrequencySum

open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums

def cutoff (n : ℕ) : Finset ℤ := Finset.Icc (-(2 ^ (n + 1))) (2 ^ (n + 1))

theorem mem_cutoff (n : ℕ) (k : ℤ) : k ∈ cutoff n ↔ |k| ≤ 2 ^ (n + 1) := by
  simp only [cutoff, Finset.mem_Icc, abs_le]

theorem mem_cutoff_real (n : ℕ) (k : ℤ) :
    k ∈ cutoff n ↔ |(k : ℝ)| ≤ (2 : ℝ) ^ (n + 1) := by
  rw [mem_cutoff]
  exact_mod_cast (Iff.rfl : |k| ≤ 2 ^ (n + 1) ↔ |k| ≤ 2 ^ (n + 1))

theorem cutoff_disjoint (n : ℕ) :
    Disjoint (cutoff n) (signedModes ((2 : ℝ) ^ (n + 1))) := by
  rw [Finset.disjoint_left]
  intro k hk hl
  exact not_lt_of_ge ((mem_cutoff_real n k).mp hk)
    ((mem_signedModes (by positivity)).mp hl).1

theorem cutoff_succ (n : ℕ) :
    cutoff (n + 1) = cutoff n ∪ signedModes ((2 : ℝ) ^ (n + 1)) := by
  ext k
  rw [Finset.mem_union, mem_cutoff_real, mem_cutoff_real,
    mem_signedModes (by positivity), pow_succ]
  have hp : (0 : ℝ) ≤ 2 ^ (n + 1) := by positivity
  constructor
  · intro hk
    by_cases hsmall : |(k : ℝ)| ≤ (2 : ℝ) ^ (n + 1)
    · exact Or.inl hsmall
    · exact Or.inr ⟨lt_of_not_ge hsmall, by linarith⟩
  · rintro (hk | ⟨_, hk⟩) <;> linarith

theorem covers (S : Finset ℤ) : ∃ n : ℕ, S ⊆ cutoff n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ k ∈ S, k.natAbs)
    (by norm_num : 1 < (2 : ℕ))
  refine ⟨n, fun k hk => ?_⟩
  have hb : k.natAbs ≤ (2 : ℕ) ^ (n + 1) :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le j.natAbs) hk).trans
      (hn.le.trans (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega)))
  rw [mem_cutoff]
  have hi : (k.natAbs : ℤ) ≤ (2 : ℤ) ^ (n + 1) := by exact_mod_cast hb
  simpa only [Int.natCast_natAbs] using hi

theorem partial_bound {f : ℤ → ℝ} {B u : ℝ}
    (hband : ∀ n : ℕ, (∑ k ∈ signedModes ((2 : ℝ) ^ (n + 1)), f k) ≤
      B * SmoothDyadicKernel.term u n) (n : ℕ) :
    (∑ k ∈ cutoff n, f k) ≤ (∑ k ∈ cutoff 0, f k) +
      B * ∑ r ∈ Finset.range n, SmoothDyadicKernel.term u r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cutoff_succ, Finset.sum_union (cutoff_disjoint n), Finset.sum_range_succ, mul_add]
    linarith [hband n]

theorem total_bound {f : ℤ → ℝ} {B u : ℝ} (hf : ∀ k, 0 ≤ f k)
    (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hband : ∀ n : ℕ, (∑ k ∈ signedModes ((2 : ℝ) ^ (n + 1)), f k) ≤
      B * SmoothDyadicKernel.term u n) :
    (∑' k : ℤ, f k) ≤ (∑ k ∈ cutoff 0, f k) + 2 * B := by
  apply Real.tsum_le_of_sum_le hf
  intro S
  obtain ⟨n, hn⟩ := covers S
  calc
    _ ≤ ∑ k ∈ cutoff n, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hn (fun k _ _ => hf k)
    _ ≤ (∑ k ∈ cutoff 0, f k) + B * ∑ r ∈ Finset.range n, SmoothDyadicKernel.term u r :=
      partial_bound hband n
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (SmoothDyadicKernel.partial_le_two hu n) hB
      linarith

end Cubic.BoxAsymptotic.SmoothFrequencySum
