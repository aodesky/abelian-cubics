import Cubic.PoissonSummation.IntegralHeightNormalization
import Cubic.PoissonSummation.HeightZetaFullRegion
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Regrouping the original height series by actual finite fibers

Absolute convergence, proved without Poisson, forces each positive-index
fiber to be finite: its summands at `s=4` have a fixed positive norm. We then
regroup by the independently constructed index using mathlib's fiberwise
summation theorem. The coefficients are actual height-fiber cardinalities.
No coefficient identity or Euler product is used here.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightCountingSeries

open AdelicHeightZetaData IntegralHeightIndex IntegralHeightNormalization HeightCountingData

abbrev IndexFiber (n : ℕ) := {P : IntegralRationalPoints // index P = n}

theorem index_fiber_finite (n : ℕ) : Finite (IndexFiber n) := by
  by_cases hn : n = 0
  · subst n
    haveI : IsEmpty (IndexFiber 0) := ⟨fun P => (index_pos P.val).ne' P.property⟩
    letI : Fintype (IndexFiber 0) := Fintype.ofIsEmpty
    exact Finite.of_fintype (IndexFiber 0)
  · have h := (HeightZetaFullRegion.series_absolute 4 0 (by norm_num)).subtype
      (fun P => index P = n)
    have he : (fun P : IndexFiber n => ‖zetaTerm 4 0 P.val‖) =
        fun _ => ‖(n : ℂ) ^ (-(4 / 2 : ℂ))‖ := by
      funext P
      rw [zetaTerm_eq, P.property]
    change Summable (fun P : IndexFiber n => ‖zetaTerm 4 0 P.val‖) at h
    rw [he] at h
    apply Finite.of_summable_const (b := ‖(n : ℂ) ^ (-(4 / 2 : ℂ))‖) _ h
    apply norm_pos_iff.mpr
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    exact Complex.exp_ne_zero _

theorem pointHeight_eq_sqrt_iff (P : IntegralRationalPoints) (n : ℕ) :
    pointHeight P = (Real.sqrt n : ℂ) ↔ index P = n := by
  rw [pointHeight_eq_sqrt_index, Complex.ofReal_inj,
    Real.sqrt_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _), Nat.cast_inj]

def fiberEquiv (n : ℕ) : Fiber n ≃ IndexFiber n :=
  Equiv.subtypeEquivRight (fun P => pointHeight_eq_sqrt_iff P n)

theorem fiber_finite (n : ℕ) : Finite (Fiber n) := by
  haveI := index_fiber_finite n
  exact Finite.of_equiv _ (fiberEquiv n).symm

theorem count_eq_index_card (n : ℕ) : count n = Nat.card (IndexFiber n) :=
  Nat.card_congr (fiberEquiv n)

theorem index_fiber_empty_of_three_dvd (n : ℕ) (hn : 3 ∣ n) : IsEmpty (IndexFiber n) :=
  ⟨fun P => three_not_dvd_index P.val (by simpa only [P.property] using hn)⟩

theorem count_eq_zero_of_three_dvd (n : ℕ) (hn : 3 ∣ n) : count n = 0 := by
  haveI := index_fiber_empty_of_three_dvd n hn
  rw [count_eq_index_card]
  exact Nat.card_of_isEmpty

theorem count_zero : count 0 = 0 := count_eq_zero_of_three_dvd 0 (dvd_zero 3)

theorem fiber_sum (s : ℂ) (n : ℕ) :
    (∑' P : IndexFiber n, zetaTerm s 0 P.val) =
      LSeries.term (fun n => (count n : ℂ)) (s / 2) n := by
  haveI := index_fiber_finite n
  letI : Fintype (IndexFiber n) := Fintype.ofFinite _
  by_cases hn : n = 0
  · subst n
    haveI := index_fiber_empty_of_three_dvd 0 (dvd_zero 3)
    simp
  · have he : (fun P : IndexFiber n => zetaTerm s 0 P.val) =
        fun _ => (n : ℂ) ^ (-(s / 2)) := by
      funext P
      rw [zetaTerm_eq, P.property]
    rw [he, LSeries.term_of_ne_zero hn, count_eq_index_card, Complex.cpow_neg]
    simp [div_eq_mul_inv]

theorem fiber_norm_sum (s : ℂ) (n : ℕ) :
    (∑' P : IndexFiber n, ‖zetaTerm s 0 P.val‖) =
      ‖LSeries.term (fun n => (count n : ℂ)) (s / 2) n‖ := by
  haveI := index_fiber_finite n
  letI : Fintype (IndexFiber n) := Fintype.ofFinite _
  by_cases hn : n = 0
  · subst n
    haveI := index_fiber_empty_of_three_dvd 0 (dvd_zero 3)
    simp
  · have he : (fun P : IndexFiber n => ‖zetaTerm s 0 P.val‖) =
        fun _ => ‖(n : ℂ) ^ (-(s / 2))‖ := by
      funext P
      rw [zetaTerm_eq, P.property]
    rw [he, LSeries.term_of_ne_zero hn, count_eq_index_card, Complex.cpow_neg]
    simp [div_eq_mul_inv]

theorem absolute (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n => (count n : ℂ)) (s / 2) := by
  have h := (HeightZetaFullRegion.series_absolute s 0 (by simpa using hs)).hasSum.tsum_fiberwise index
  have he : (fun n : ℕ => ∑' P : index ⁻¹' {n}, ‖zetaTerm s 0 P.val‖) =
      fun n => ‖LSeries.term (fun n => (count n : ℂ)) (s / 2) n‖ := by
    funext n
    exact fiber_norm_sum s n
  rw [he] at h
  exact h.summable.of_norm

theorem heightZeta_eq_LSeries (s : ℂ) (hs : 2 < s.re) :
    heightZeta s 0 = LSeries (fun n => (count n : ℂ)) (s / 2) := by
  have h := (HeightZetaFullRegion.series_absolute s 0 (by simpa using hs)).of_norm.hasSum.tsum_fiberwise index
  have he : (fun n : ℕ => ∑' P : index ⁻¹' {n}, zetaTerm s 0 P.val) =
      LSeries.term (fun n => (count n : ℂ)) (s / 2) := by
    funext n
    exact fiber_sum s n
  rw [he] at h
  exact h.tsum_eq.symm

end Cubic.PoissonSummation.HeightCountingSeries
