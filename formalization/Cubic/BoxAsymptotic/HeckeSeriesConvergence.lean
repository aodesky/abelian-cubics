import Cubic.BoxAsymptotic.AngularMomentData
import Cubic.BoxAsymptotic.HeckeGeneratorPhases
import Cubic.PoissonSummation.DedekindZetaSeries

/-! Absolute convergence of the actual Hecke series, and equality of its ideal
and integer-norm presentations. The proof uses the Dedekind-zeta majorant; it
requires neither an Euler product nor a functional equation. -/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeSeriesConvergence

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.AngularMomentData

local notation "Z" => Cubic.PoissonSummation.DedekindZetaSeries.coefficient E

def coefficient (χ : Ideal Integers → ℂ) (n : ℕ) : ℂ :=
  ∑ᶠ I ∈ {I : Ideal Integers | Ideal.absNorm I = n}, χ I

def idealTerm (χ : Ideal Integers → ℂ) (s : ℂ) (I : Ideal Integers) : ℂ :=
  χ I * Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E s I

theorem coefficient_bound (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (n : ℕ) :
    ‖coefficient χ n‖ ≤ Z n := by
  classical
  rw [coefficient, finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOf_absNorm_eq n)]
  calc
    _ ≤ ∑ I ∈ (Ideal.finite_setOf_absNorm_eq n).toFinset, ‖χ I‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ (Ideal.finite_setOf_absNorm_eq n).toFinset, (1 : ℝ) :=
      Finset.sum_le_sum (fun I _ => hχ I)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← Set.ncard_eq_toFinset_card {I : Ideal Integers | Ideal.absNorm I = n}
        (Ideal.finite_setOf_absNorm_eq n)]
      rfl

theorem coefficient_summable (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coefficient χ) s := by
  have h := (Cubic.PoissonSummation.DedekindZetaSeries.coefficient_summable E s hs).norm
  rw [LSeriesSummable, ← summable_norm_iff]
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => LSeries.norm_term_le s ?_
  have hZ : 0 ≤ Z n := Nat.cast_nonneg _
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZ] using
    coefficient_bound χ hχ n

theorem ideal_series_absolute (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I => ‖idealTerm χ s I‖) := by
  apply (Cubic.PoissonSummation.DedekindZetaSeries.ideal_series_absolute E s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  rw [idealTerm, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hχ I)

theorem fiber_sum (χ : Ideal Integers → ℂ) (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal Integers // Ideal.absNorm I = n}, idealTerm χ s I) =
      LSeries.term (coefficient χ) s n := by
  haveI : Finite {I : Ideal Integers // Ideal.absNorm I = n} :=
    Ideal.finite_setOf_absNorm_eq n
  have he : (fun I : {I : Ideal Integers // Ideal.absNorm I = n} => idealTerm χ s I) =
      fun I : {I : Ideal Integers // Ideal.absNorm I = n} =>
        χ I.val * LSeries.term (fun _ => 1) s n := by
    funext I
    simp only [idealTerm, Cubic.PoissonSummation.DedekindZetaSeries.idealTerm, I.property]
  rw [he, tsum_mul_right, tsum_eq_finsum (Set.toFinite _),
    finsum_subtype_eq_finsum_cond (f := χ) (fun I => Ideal.absNorm I = n)]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.term_of_ne_zero hn, div_eq_mul_inv, coefficient, one_mul,
      Set.mem_setOf_eq]

theorem sum_ideals (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' I, idealTerm χ s I) = LSeries (coefficient χ) s := by
  have h := (ideal_series_absolute χ hχ s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  have he : (fun n : ℕ => ∑' I : Ideal.absNorm ⁻¹' {n}, idealTerm χ s I.val) =
      LSeries.term (coefficient χ) s := by
    funext n
    exact fiber_sum χ s n
  rw [he] at h
  exact h.tsum_eq.symm

theorem norm_psi_le (k : ℤ) (I : Ideal Integers) : ‖psi k I‖ ≤ 1 := by
  by_cases hI : 3 ∣ Ideal.absNorm I
  · simp [psi, hI]
  · exact (norm_psi k I hI).le

theorem norm_generatorPhase_le (k : ℤ) (I : Ideal Integers) : ‖generatorPhase k I‖ ≤ 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [generatorPhase, hI]
  · simp [generatorPhase, hI]

theorem norm_primitivePsi_le (k : ℤ) (I : Ideal Integers) : ‖primitivePsi k I‖ ≤ 1 := by
  unfold primitivePsi
  split_ifs
  · exact norm_generatorPhase_le k I
  · exact norm_psi_le k I

theorem hecke_summable (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (heckeCoefficient k) s :=
  coefficient_summable (psi k) (norm_psi_le k) s hs

theorem hecke_sum_ideals (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    (∑' I, idealTerm (psi k) s I) = heckeSeries k s :=
  sum_ideals (psi k) (norm_psi_le k) s hs

end Cubic.BoxAsymptotic.HeckeSeriesConvergence
