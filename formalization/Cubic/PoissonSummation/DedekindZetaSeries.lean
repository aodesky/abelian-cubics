import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Absolute convergence of the genuine Dedekind zeta series

Use mathlib's asymptotic count of integral ideals to establish absolute
convergence on `Re(s)>1`. The coefficients are the actual cardinalities
of ideal-norm fibers. No proposed Euler product is used to define them.

The summatory identity follows the same finite-fiber calculation as
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` in mathlib.
-/

noncomputable section

namespace Cubic.PoissonSummation.DedekindZetaSeries

open Filter Ideal NumberField Asymptotics
open scoped Topology nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

def coefficient (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem summatory_limit : Tendsto
    (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, coefficient K k) / (n : ℝ))
    atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, coefficient, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem coefficient_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coefficient K n : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
    (f := coefficient K) ?_ (fun _ => Nat.cast_nonneg _) (by norm_num) hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using summatory_limit K)

/-- The zero ideal contributes zero, as does index zero in mathlib's `LSeries`. -/
def idealTerm (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  LSeries.term (fun _ => 1) s (Ideal.absNorm I)

theorem coefficient_term (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (coefficient K n : ℂ)) s n =
      (coefficient K n : ℂ) * LSeries.term (fun _ => 1) s n := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [LSeries.term_of_ne_zero hn, div_eq_mul_inv]

theorem fiber_sum (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, idealTerm K s I) =
      LSeries.term (fun n => (coefficient K n : ℂ)) s n := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    Ideal.finite_setOf_absNorm_eq n
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} => idealTerm K s I) =
      fun _ => LSeries.term (fun _ => 1) s n := by
    funext I
    simp only [idealTerm, I.property]
  rw [he, coefficient_term]
  simp [coefficient]

theorem fiber_norm_sum (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, ‖idealTerm K s I‖) =
      ‖LSeries.term (fun n => (coefficient K n : ℂ)) s n‖ := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    Ideal.finite_setOf_absNorm_eq n
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} => ‖idealTerm K s I‖) =
      fun _ => ‖LSeries.term (fun _ => 1) s n‖ := by
    funext I
    simp only [idealTerm, I.property]
  rw [he, coefficient_term, norm_mul]
  simp [coefficient]

theorem ideal_series_absolute (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) => ‖idealTerm K s I‖) := by
  rw [summable_partition (s := fun n : ℕ => {I : Ideal (𝓞 K) | Ideal.absNorm I = n})
    (fun I => norm_nonneg _) (fun I => ⟨Ideal.absNorm I, rfl, fun n hn => hn.symm⟩)]
  constructor
  · intro n
    haveI : Finite ↥{I : Ideal (𝓞 K) | Ideal.absNorm I = n} :=
      Ideal.finite_setOf_absNorm_eq n
    exact summable_of_finite_support (Set.toFinite _)
  · change Summable (fun n => ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, ‖idealTerm K s I‖)
    simpa only [fiber_norm_sum] using (coefficient_summable K s hs).norm

theorem sum_ideals (s : ℂ) (hs : 1 < s.re) :
    (∑' I : Ideal (𝓞 K), idealTerm K s I) = NumberField.dedekindZeta K s := by
  have h := (ideal_series_absolute K s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  have he : (fun n : ℕ => ∑' I : Ideal.absNorm ⁻¹' {n}, idealTerm K s I.val) =
      LSeries.term (fun n => (coefficient K n : ℂ)) s := by
    funext n
    exact fiber_sum K s n
  rw [he] at h
  simpa only [NumberField.dedekindZeta, coefficient, Complex.ofReal_natCast, LSeries] using h.tsum_eq.symm

end Cubic.PoissonSummation.DedekindZetaSeries
