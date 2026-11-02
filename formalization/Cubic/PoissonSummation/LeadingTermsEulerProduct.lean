import Cubic.PoissonSummation.LeadingTermsSplitProduct
import Cubic.PoissonSummation.HeightZetaEulerExtraction
import Cubic.PoissonSummation.QuadraticDedekindResidue
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Extracting `1/ζ(s)` from the correction product

Combine the ordinary factors over inert and split primes, removing the
prime 3 explicitly. This yields the simplified Euler product in the proof
of `prop:leadingTerms`, and its value at 2. Every infinite product used in
the rearrangement has a proved `HasProd` or `Multipliable` hypothesis.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsEulerProduct

open FiniteEulerProduct

theorem inverse_zeta_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 - (p : ℂ) ^ (-s)) (1 / riemannZeta s) := by
  have h := Filter.Tendsto.inv₀ (riemannZeta_eulerProduct_hasProd hs)
    (riemannZeta_ne_zero_of_one_lt_re hs)
  simpa only [HasProd, Function.comp_def, ← Finset.prod_inv_distrib, inv_inv, one_div] using h

theorem ordinary_multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes => 1 - (p : ℂ) ^ (-s)) :=
  (inverse_zeta_hasProd hs).multipliable

theorem ordinary_inert_multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun q : InertPrimes => 1 - (q.1 : ℂ) ^ (-s)) := by
  have h : Summable (fun q : InertPrimes => ‖(1 - (q.1 : ℂ) ^ (-s)) - 1‖) := by
    simpa using (summable_prime_power hs).subtype (fun p => (p : ℕ) % 3 = 2)
  simpa using multipliable_one_add_of_summable h

theorem ordinary_split_multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : SplitPrimes => 1 - (p.1 : ℂ) ^ (-s)) := by
  have h : Summable (fun p : SplitPrimes => ‖(1 - (p.1 : ℂ) ^ (-s)) - 1‖) := by
    simpa using (summable_prime_power hs).subtype (fun p => (p : ℕ) % 3 = 1)
  simpa using multipliable_one_add_of_summable h

theorem inverse_zeta_without_three (s : ℂ) (hs : 1 < s.re) :
    (1 - (3 : ℂ) ^ (-s)) * (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-s))) *
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-s))) = 1 / riemannZeta s := by
  exact (hasProd_primes_mod_three (f := fun p : Nat.Primes => 1 - (p : ℂ) ^ (-s))
    (ordinary_inert_multipliable s hs).hasProd
    (ordinary_split_multipliable s hs).hasProd).unique (inverse_zeta_hasProd hs)

theorem split_product_identity (s : ℂ) (hs : 1 < s.re) :
    (∏' p : SplitPrimes, HeightZetaCorrectionProduct.split p (s / 2)) =
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-s))) *
        ∏' p : SplitPrimes, LeadingTermsData.splitFactor p s := by
  simp_rw [LeadingTermsSplitProduct.local_identity _ hs]
  exact (ordinary_split_multipliable s hs).tprod_mul
    (LeadingTermsSplitProduct.multipliable s hs)

/-- The paper's simplified product, with `2z=s` kept explicit in the zeta argument. -/
theorem correction_formula (s : ℂ) (hs : 1 < s.re) :
    LeadingTermsData.correction s =
      ((1 - (3 : ℂ) ^ (-(s / 2))) / (1 + (3 : ℂ) ^ (-(s / 2)))) *
        (1 / riemannZeta s) * ∏' p : SplitPrimes, LeadingTermsData.splitFactor p s := by
  have hx := LeadingTermsSplitProduct.inversePower_add_ne_zero primeThree hs
  have hpow : (3 : ℂ) ^ (-s) = ((3 : ℂ) ^ (-(s / 2))) ^ 2 :=
    LeadingTermsSplitProduct.inversePower_sq primeThree s
  have hI : (∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q (s / 2)) =
      ∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-s)) := by
    unfold HeightZetaCorrectionProduct.inert
    apply tprod_congr
    intro q
    rw [show (2 : ℂ) * (s / 2) = s by ring]
  rw [LeadingTermsData.correction, HeightZetaCorrectionProduct.value, hI,
    split_product_identity s hs, ← inverse_zeta_without_three s hs, hpow]
  change 1 + (3 : ℂ) ^ (-(s / 2)) ≠ 0 at hx
  field_simp
  ring

theorem correction_two_explicit : LeadingTermsData.correction 2 =
    (3 / (Real.pi : ℂ) ^ 2) * LeadingTermsData.splitProductAtTwo := by
  rw [correction_formula 2 (by norm_num), riemannZeta_two]
  norm_num [Complex.cpow_neg, LeadingTermsData.splitFactor, LeadingTermsData.splitProductAtTwo]
  left
  ring

/-- The numerical leading coefficient follows from the genuine class-number-formula residue. -/
theorem residue_leading_explicit :
    4 * (NumberField.dedekindZeta_residue Cubic.QuadraticCorrespondence.CyclotomicField.E : ℂ) ^ 2 *
      LeadingTermsData.correction 2 = (4 / 9 : ℂ) * LeadingTermsData.splitProductAtTwo := by
  rw [QuadraticDedekindResidue.residue_value_complex, correction_two_explicit]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsqrt : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt0 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp
  rw [hsqrt]
  ring

end Cubic.PoissonSummation.LeadingTermsEulerProduct
