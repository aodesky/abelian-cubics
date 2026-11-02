import Cubic.BoxAsymptotic.ZeroModeMass
import Cubic.Counting.MonicConceptualConstants
import Cubic.BoxAsymptotic.CoefficientConvergence
import Cubic.PoissonSummation.HeightCountingEulerProduct
import Cubic.PoissonSummation.HeightZetaContinuationFormula
import Cubic.PoissonSummation.QuadraticZetaRegularization

/-! Absolute convergence and Euler product of the actual zero-mode series in `eq:F0`.
Absolute convergence follows from the fourfold divisor majorant, and the
Euler product follows directly from the split and inert prime-power coefficients. -/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroModeSeries

open Cubic.PoissonSummation Cubic.BoxAsymptotic.ZeroModeData
open Cubic.Counting.MonicConceptualConstants

abbrev AwayThree := {m : ℕ // ¬ 3 ∣ m}

theorem away_pos (m : AwayThree) : 0 < m.1 := by
  by_contra h
  have : m.1 = 0 := by omega
  exact m.2 (this ▸ dvd_zero 3)

theorem decomposition_injective :
    Function.Injective (fun p : ℕ × AwayThree => 3 ^ p.1 * p.2.1) := by
  suffices ∀ e f : ℕ, ∀ m n : AwayThree, 3 ^ e * m.1 = 3 ^ f * n.1 → e = f ∧ m = n by
    intro p q h; exact Prod.ext (this _ _ _ _ h).1 (this _ _ _ _ h).2
  intro e
  induction e with
  | zero =>
    intro f m n h
    cases f with
    | zero => exact ⟨rfl, Subtype.ext (by simpa using h)⟩
    | succ f =>
      have hm : 3 ∣ m.1 := by
        simp only [pow_zero, one_mul] at h
        rw [h]
        exact dvd_mul_of_dvd_left (dvd_pow_self 3 (Nat.succ_ne_zero f)) n.1
      exact (m.2 hm).elim
  | succ e ih =>
    intro f m n h
    cases f with
    | zero =>
      have hn : 3 ∣ n.1 := by
        simp only [pow_zero, one_mul] at h
        rw [← h]
        exact dvd_mul_of_dvd_left (dvd_pow_self 3 (Nat.succ_ne_zero e)) m.1
      exact (n.2 hn).elim
    | succ f =>
      have heq : 3 ^ e * m.1 = 3 ^ f * n.1 := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
        convert h using 1 <;> ring
      obtain ⟨hef, hmn⟩ := ih f m n heq
      exact ⟨congrArg Nat.succ hef, hmn⟩

/-- Unique decomposition `n = 3^e M`, with `3 ∤ M`, for positive integers. -/
def decomposition : (ℕ × AwayThree) ≃ {n : ℕ // n ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨3 ^ p.1 * p.2.1, by have := away_pos p.2; positivity⟩)
    ⟨fun _ _ h => decomposition_injective (congrArg Subtype.val h), by
      intro n
      obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd n.2 3 (by norm_num)
      exact ⟨(e, ⟨m, hm⟩), Subtype.ext he.symm⟩⟩

def localTerm (s : ℂ) (e : ℕ) : ℂ :=
  (if e < 2 then (1 / 3 : ℂ) else 1) * ((3 : ℂ) ^ (-s)) ^ e

set_option maxHeartbeats 800000 in
theorem local_hasSum (s : ℂ) (hs : 1 < s.re) : HasSum (localTerm s) (R s) := by
  let q : ℂ := (3 : ℂ) ^ (-s)
  have hq : ‖q‖ < 1 := by
    exact (Complex.norm_prime_cpow_le_one_half ⟨3, Nat.prime_three⟩ hs).trans_lt (by norm_num)
  have htail : HasSum (fun e => localTerm s (e + 1 + 1)) (q ^ 2 / (1 - q)) := by
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left (q ^ 2) using 1
    · funext e
      simp only [localTerm, if_neg (show ¬ e + 1 + 1 < 2 by omega), one_mul, pow_succ]
      dsimp [q]; ring
  have h := htail.zero_add.zero_add
  have hne : 1 - q ≠ 0 := Cubic.Counting.MonicEulerFactor.three_sub_ne_zero (by linarith)
  convert h using 1
  simp only [localTerm, show (1 : ℕ) < 2 by decide, show (0 : ℕ) < 2 by decide,
    if_true, Nat.zero_add, pow_one, pow_zero, mul_one]
  rw [R, Cubic.Counting.MonicEulerFactor.three_sq]
  change (1 + 2 * q ^ 2) / (3 * (1 - q)) = 1 / 3 + (1 / 3 * q + q ^ 2 / (1 - q))
  field_simp
  ring

theorem away_hasSum
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun m : AwayThree => (HeightCountingCoefficients.coefficient m.1 : ℂ) *
      (m.1 : ℂ) ^ (-s))
      (QuadraticZetaRegularization.value s ^ 2 * LeadingTermsData.correction (2 * s)) := by
  have hsum := CoefficientConvergence.summable s hs
  have heq : LSeries (fun n => (HeightCountingCoefficients.coefficient n : ℂ)) s =
      QuadraticZetaRegularization.value s ^ 2 * LeadingTermsData.correction (2 * s) := by
    rw [HeightCountingEulerProduct.euler_product_of_summable s hs hsum,
      ← HeightZetaContinuationFormula.continuation_eq_eulerExpression s hs]
    unfold HeightZetaContinuation.value QuadraticZetaRegularization.value LeadingTermsData.correction
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
    ring
  have hsupport : Function.support
      (LSeries.term (fun n => (HeightCountingCoefficients.coefficient n : ℂ)) s) ⊆
      {m : ℕ | ¬ 3 ∣ m} := by
    intro m hm hd
    apply hm
    simp only [LSeries.term_def, HeightCountingCoefficients.coefficient_apply,
      hd, if_true, Int.cast_zero, zero_div, ite_self]
  have hfull : HasSum (LSeries.term (fun n => (HeightCountingCoefficients.coefficient n : ℂ)) s)
      (QuadraticZetaRegularization.value s ^ 2 * LeadingTermsData.correction (2 * s)) := by
    rw [← heq]; exact hsum.hasSum
  have hh := (hasSum_subtype_iff_of_support_subset hsupport).mpr hfull
  convert hh using 1
  funext m
  exact (LSeries.term_def₀
    (f := fun n => (HeightCountingCoefficients.coefficient n : ℂ)) (by simp) s m.1).symm

theorem term_factor (s : ℂ) (p : ℕ × AwayThree) :
    localTerm s p.1 *
      ((HeightCountingCoefficients.coefficient p.2.1 : ℂ) * (p.2.1 : ℂ) ^ (-s)) =
      LSeries.term (fun n => (mass n : ℂ)) s (decomposition p).1 := by
  rw [LSeries.term_of_ne_zero (decomposition p).2, div_eq_mul_inv, ← Complex.cpow_neg]
  change _ = (mass (3 ^ p.1 * p.2.1) : ℂ) * ((3 ^ p.1 * p.2.1 : ℕ) : ℂ) ^ (-s)
  rw [ZeroModeMass.«eq:mass» _ _ (away_pos p.2) p.2.2]
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    HeightCountingEulerProduct.nat_pow_cpow]
  simp only [localTerm]
  split_ifs <;> push_cast <;> ring

theorem series_hasSum
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (fun n => (mass n : ℂ)) s) (continuation s) := by
  have hL := local_hasSum s hs
  have hA := away_hasSum s hs
  have hnorm := summable_mul_of_summable_norm (f := localTerm s)
    (g := fun m : AwayThree => (HeightCountingCoefficients.coefficient m.1 : ℂ) * (m.1 : ℂ) ^ (-s))
    hL.summable.norm hA.summable.norm
  have hprod := hL.mul hA hnorm
  have heq : (fun p : ℕ × AwayThree => localTerm s p.1 *
      ((HeightCountingCoefficients.coefficient p.2.1 : ℂ) * (p.2.1 : ℂ) ^ (-s))) =
      (fun p => LSeries.term (fun n => (mass n : ℂ)) s (decomposition p).1) := by
    funext p
    exact term_factor s p
  rw [heq] at hprod
  have hpos := (decomposition.hasSum_iff
    (f := fun n : {n : ℕ // n ≠ 0} => LSeries.term (fun n => (mass n : ℂ)) s n.1)).mp hprod
  have hsupp : Function.support (LSeries.term (fun n => (mass n : ℂ)) s) ⊆
      {n : ℕ | n ≠ 0} := by
    intro n hn h0; subst n; simp at hn
  have hsum := (hasSum_subtype_iff_of_support_subset hsupp).mp hpos
  convert hsum using 1
  rw [continuation, localFactor, R, LeadingTermsData.correction]
  have hne := Cubic.Counting.MonicEulerFactor.three_sub_ne_zero (z := s) (by linarith)
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  field_simp

end Cubic.BoxAsymptotic.ZeroModeSeries
