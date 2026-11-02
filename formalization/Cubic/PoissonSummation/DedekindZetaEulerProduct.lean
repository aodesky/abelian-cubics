import Cubic.PoissonSummation.DedekindZetaSeries
import Cubic.PoissonSummation.IdealEulerSieve
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# The Euler product of the actual Dedekind zeta series

Apply the absolutely convergent sieve to integral ideals and their actual
absolute norms. Unique factorization supplies a prime divisor of every
nonzero nonunit ideal. In particular this proves nonvanishing and the
Euler product without replacing the ideal-counting definition.
-/

noncomputable section

namespace Cubic.PoissonSummation.DedekindZetaEulerProduct

open NumberField Ideal Filter
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

abbrev PrimeIdeals := IdealEulerSieve.Primes (Ideal (𝓞 K))

def summand (s : ℂ) (hs : s ≠ 0) : Ideal (𝓞 K) →*₀ ℂ :=
  (riemannZetaSummandHom hs).comp Ideal.absNorm

theorem summand_eq (s : ℂ) (hs : s ≠ 0) (I : Ideal (𝓞 K)) :
    summand K s hs I = DedekindZetaSeries.idealTerm K s I := by
  simp [summand, riemannZetaSummandHom, DedekindZetaSeries.idealTerm,
    LSeries.term_of_ne_zero' hs, Complex.cpow_neg]

theorem summand_absolute (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I => ‖summand K s (Complex.ne_zero_of_one_lt_re hs) I‖) := by
  simpa only [summand_eq] using DedekindZetaSeries.ideal_series_absolute K s hs

theorem prime_divisor (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hI1 : I ≠ 1) :
    ∃ P : PrimeIdeals K, P.val ∣ I := by
  have hnu : ¬ IsUnit I := by simpa using hI1
  obtain ⟨P, hP, hPI⟩ := WfDvdMonoid.exists_irreducible_factor hnu hI
  exact ⟨⟨P, hP.prime⟩, hPI⟩

theorem inverse_factors_multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun P : PrimeIdeals K => 1 - (Ideal.absNorm P.val : ℂ) ^ (-s)) := by
  have h := (DedekindZetaSeries.ideal_series_absolute K s hs).subtype (fun I => Prime I)
  have he (P : PrimeIdeals K) : DedekindZetaSeries.idealTerm K s P.val =
      (Ideal.absNorm P.val : ℂ) ^ (-s) := by
    rw [← summand_eq K s (Complex.ne_zero_of_one_lt_re hs)]
    rfl
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
    (by simpa only [norm_neg, Function.comp_def, he] using h :
      Summable (fun P : PrimeIdeals K => ‖-(Ideal.absNorm P.val : ℂ) ^ (-s)‖))

theorem sum_mul_inverse_product (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta K s *
      (∏' P : PrimeIdeals K, (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))) = 1 := by
  have h := IdealEulerSieve.sum_mul_product (summand K s (Complex.ne_zero_of_one_lt_re hs))
    (summand_absolute K s hs) (prime_divisor K)
  have he : (∑' I, summand K s (Complex.ne_zero_of_one_lt_re hs) I) =
      NumberField.dedekindZeta K s := by
    simpa only [summand_eq] using DedekindZetaSeries.sum_ideals K s hs
  rw [he] at h
  exact h

theorem ne_zero (s : ℂ) (hs : 1 < s.re) : NumberField.dedekindZeta K s ≠ 0 := by
  have h := sum_mul_inverse_product K s hs
  intro hz
  simp [hz] at h

theorem inverse_euler_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals K => 1 - (Ideal.absNorm P.val : ℂ) ^ (-s))
      (NumberField.dedekindZeta K s)⁻¹ := by
  have he : (∏' P : PrimeIdeals K, (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))) =
      (NumberField.dedekindZeta K s)⁻¹ := by
    apply (mul_left_cancel₀ (ne_zero K s hs))
    rw [sum_mul_inverse_product K s hs, mul_inv_cancel₀ (ne_zero K s hs)]
  rw [← he]
  exact (inverse_factors_multipliable K s hs).hasProd

theorem euler_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals K => (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  have h := (inverse_euler_hasProd K s hs).inv₀ (inv_ne_zero (ne_zero K s hs))
  simpa only [HasProd, Function.comp_def, ← Finset.prod_inv_distrib, inv_inv] using h

end Cubic.PoissonSummation.DedekindZetaEulerProduct
