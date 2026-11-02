import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Σ_{p ≡ 1 (mod 3)} 1/p = ∞`

Supporting fact for the box-height lower bound: the cyclic cubic fields of prime conductor
`p ≡ 1 (mod 3)` have `Σ 1/p = ∞`.

From mathlib's form of Dirichlet's theorem: for `1 < x ≤ 2`,
`Σ_{n ≡ 1 (3)} Λ(n) n^{-x} ≥ 1/(2(x-1)) - C`, and the non-prime terms are bounded. If
`Σ_{p ≡ 1} 1/p` converged, choose `T` with `Σ_{p ≡ 1, p ≥ T} 1/p ≤ 1/4`. Since
`log p ≤ p^{x-1}/(x-1)`, the primes `p ≥ T` contribute at most `1/(4(x-1))`, and those below
`T` at most `log T · Σ 1/p`. This contradicts the lower bound as `x → 1⁺`.
-/

noncomputable section

namespace Cubic.BoxHeight.PrimeReciprocals

open ArithmeticFunction ArithmeticFunction.vonMangoldt

/-- `1/p` on primes `p ≡ 1 (mod 3)`, and `0` elsewhere. -/
def f (n : ℕ) : ℝ := if n.Prime ∧ (n : ZMod 3) = 1 then 1 / (n : ℝ) else 0

theorem f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; split_ifs <;> positivity

theorem not_summable_f : ¬ Summable f := by
  intro hf
  have ha : IsUnit (1 : ZMod 3) := isUnit_one
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  set Cnp := ∑' n : ℕ, (if n.Prime then 0 else residueClass (1 : ZMod 3) n) / n
  -- the tail of `Σ f`
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∑' k : ℕ, f (k + T) ≤ 1 / 4 := by
    have := (tendsto_sum_nat_add f)
    have hev := (this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
    exact ⟨T, hT T le_rfl⟩
  set S := ∑' n, f n
  set tail := ∑' k : ℕ, f (k + T)
  have htail0 : 0 ≤ tail := tsum_nonneg fun _ => f_nonneg _
  have hT1 : (1 : ℝ) ≤ max 1 (T : ℝ) := le_max_left _ _
  set L := Real.log (max 1 (T : ℝ))
  have hL0 : 0 ≤ L := Real.log_nonneg hT1
  have hS0 : 0 ≤ S := tsum_nonneg f_nonneg
  -- the upper bound for `1 < x ≤ 2`
  have hupper : ∀ x : ℝ, 1 < x → x ≤ 2 →
      ∑' n : ℕ, residueClass (1 : ZMod 3) n / (n : ℝ) ^ x ≤ Cnp + L * S + tail / (x - 1) := by
    intro x hx1 hx2
    have hsum : Summable fun n : ℕ => residueClass (1 : ZMod 3) n / (n : ℝ) ^ x :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one (1 : ZMod 3)).trans_lt <| mod_cast hx1
    have hx0 : 0 < x - 1 := by linarith
    set tf : ℕ → ℝ := fun n => if T ≤ n then f n else 0 with htf
    have htf0 : ∀ n, 0 ≤ tf n := fun n => by simp only [htf]; split_ifs <;> [exact f_nonneg n; rfl]
    have htfs : Summable tf := hf.of_nonneg_of_le htf0 fun n => by
      simp only [htf]; split_ifs <;> [rfl; exact f_nonneg n]
    have htft : ∑' n, tf n = tail := by
      rw [← htfs.sum_add_tsum_nat_add T]
      have h0 : ∑ i ∈ Finset.range T, tf i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          simp only [htf, Finset.mem_range] at hi ⊢; rw [if_neg (by omega)]
      rw [h0, zero_add]
      exact tsum_congr fun k => by simp only [htf]; rw [if_pos (by omega)]
    have hnp := summable_residueClass_non_primes_div (1 : ZMod 3)
    set r : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass (1 : ZMod 3) n) / n +
      L * f n + tf n / (x - 1)
    have hrs : Summable r := (hnp.add (hf.mul_left L)).add (htfs.div_const _)
    have hle : ∀ n : ℕ, residueClass (1 : ZMod 3) n / (n : ℝ) ^ x ≤ r n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : residueClass (1 : ZMod 3) 0 / ((0 : ℕ) : ℝ) ^ x = 0 := by
          rw [Nat.cast_zero, Real.zero_rpow (by linarith : x ≠ 0), div_zero]
        rw [h0]
        simp only [r, Nat.cast_zero, div_zero, zero_add]
        exact add_nonneg (mul_nonneg hL0 (f_nonneg 0)) (div_nonneg (htf0 0) hx0.le)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnx : (n : ℝ) ≤ (n : ℝ) ^ x := by
        conv_lhs => rw [← Real.rpow_one (n : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hn1 hx1.le
      have hpos : (0 : ℝ) < n := by linarith
      have hr1 := mul_nonneg hL0 (f_nonneg n)
      have hr2 := div_nonneg (htf0 n) hx0.le
      by_cases hp : n.Prime
      · have hnp0 : (if n.Prime then 0 else residueClass (1 : ZMod 3) n) / n = 0 := by
          rw [if_pos hp, zero_div]
        simp only [r, hnp0, zero_add]
        by_cases h1 : (n : ZMod 3) = 1
        · have hres : residueClass (1 : ZMod 3) n = Real.log n := by
            rw [residueClass, Set.indicator_of_mem (by exact h1), vonMangoldt_apply_prime hp]
          have hfn : f n = 1 / n := by simp [f, hp, h1]
          rw [hres]
          rcases lt_or_ge n T with hnT | hnT
          · have hlog : Real.log n ≤ L :=
              Real.log_le_log hpos (le_trans (by exact_mod_cast hnT.le) (le_max_right _ _))
            have : Real.log n / (n : ℝ) ^ x ≤ L * f n := by
              rw [hfn, mul_one_div]
              exact div_le_div₀ hL0 hlog hpos hnx
            linarith
          · have htfn : tf n = f n := by simp only [htf]; rw [if_pos hnT]
            have hlog := Real.log_le_rpow_div hpos.le hx0
            have hsplit : (n : ℝ) ^ x = n * (n : ℝ) ^ (x - 1) := by
              rw [← Real.rpow_one_add' hpos.le (by linarith)]; ring_nf
            have hpow : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hpos _
            have : Real.log n / (n : ℝ) ^ x ≤ tf n / (x - 1) := by
              rw [htfn, hfn, hsplit, div_le_div_iff₀ (by positivity) hx0]
              calc Real.log n * (x - 1) ≤ (n : ℝ) ^ (x - 1) / (x - 1) * (x - 1) :=
                    mul_le_mul_of_nonneg_right hlog hx0.le
                _ = 1 * (n * (n : ℝ) ^ (x - 1)) / n := by field_simp
                _ = _ := by ring
            linarith
        · have hres : residueClass (1 : ZMod 3) n = 0 :=
            Set.indicator_of_notMem (by exact h1) _
          rw [hres, zero_div]; linarith
      · have hnp0 : (if n.Prime then 0 else residueClass (1 : ZMod 3) n) / n =
            residueClass (1 : ZMod 3) n / n := by rw [if_neg hp]
        have hfn : f n = 0 := by simp [f, hp]
        have htfn : tf n = 0 := by simp only [htf]; split_ifs <;> [exact hfn; rfl]
        simp only [r, hnp0, hfn, htfn, mul_zero, zero_div, add_zero]
        exact div_le_div_of_nonneg_left (residueClass_nonneg _ _) hpos hnx
    calc ∑' n : ℕ, residueClass (1 : ZMod 3) n / (n : ℝ) ^ x ≤ ∑' n, r n :=
          Summable.tsum_le_tsum hle hsum hrs
      _ = Cnp + L * S + tail / (x - 1) := by
          rw [(hnp.add (hf.mul_left L)).tsum_add (htfs.div_const _), hnp.tsum_add (hf.mul_left L),
            tsum_mul_left, tsum_div_const, htft]
  -- the contradiction as `x → 1⁺`
  set K := Cnp + L * S + C'
  obtain ⟨x, hx1, hx2, hxK⟩ : ∃ x : ℝ, 1 < x ∧ x ≤ 2 ∧ K * (x - 1) < 1 / 4 := by
    have hm : min 1 (1 / (8 * (|K| + 1))) ≤ 1 / (8 * (|K| + 1)) := min_le_right _ _
    have hm0 : 0 < min 1 (1 / (8 * (|K| + 1))) := lt_min one_pos (by positivity)
    refine ⟨1 + min 1 (1 / (8 * (|K| + 1))), by linarith, by
      linarith [min_le_left 1 (1 / (8 * (|K| + 1)))], ?_⟩
    rw [add_sub_cancel_left]
    calc K * min 1 (1 / (8 * (|K| + 1))) ≤ |K| * min 1 (1 / (8 * (|K| + 1))) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hm0.le
      _ ≤ (|K| + 1) * (1 / (8 * (|K| + 1))) :=
          mul_le_mul (by linarith) hm hm0.le (by positivity)
      _ = 1 / 8 := by field_simp
      _ < 1 / 4 := by norm_num
  have hlow := hC' (x := x) ⟨hx1, hx2⟩
  have hup := hupper x hx1 hx2
  have hx0 : 0 < x - 1 := by linarith
  have htot : ((3 : ℕ).totient : ℝ)⁻¹ = 1 / 2 := by
    rw [Nat.totient_prime Nat.prime_three]; norm_num
  rw [htot] at hlow
  have h1 : 1 / 2 / (x - 1) - C' ≤ Cnp + L * S + 1 / 4 / (x - 1) := by
    have : tail / (x - 1) ≤ 1 / 4 / (x - 1) := div_le_div_of_nonneg_right hT hx0.le
    linarith
  have h2 : 1 / 4 ≤ K * (x - 1) := by
    have e : (1 / 2 / (x - 1) - 1 / 4 / (x - 1)) * (x - 1) = 1 / 4 := by field_simp; ring
    have := mul_le_mul_of_nonneg_right (by linarith : 1 / 2 / (x - 1) - 1 / 4 / (x - 1) ≤ K) hx0.le
    linarith
  linarith

end Cubic.BoxHeight.PrimeReciprocals
