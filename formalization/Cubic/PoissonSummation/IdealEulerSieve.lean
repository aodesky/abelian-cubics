import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Removing prime factors from an absolutely convergent multiplicative sum

This is the Euler-product argument needed for the actual ideal series.
Removing one prime multiplies the sum by `1 - f p`. After removing all
primes, only the unit remains. Absolute convergence justifies both the
reindexing of the divisible terms and the limiting argument.
-/

noncomputable section

namespace Cubic.PoissonSummation.IdealEulerSieve

open Filter
open scoped Topology Classical

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
  [Subsingleton Mˣ]

abbrev Primes (M : Type*) [CommMonoidWithZero M] := {p : M // Prime p}

def sifted (f : M →*₀ ℂ) (S : Finset (Primes M)) (x : M) : ℂ :=
  if ∀ p ∈ S, ¬ p.val ∣ x then f x else 0

omit [IsCancelMulZero M] [Subsingleton Mˣ] in
theorem sifted_norm_le (f : M →*₀ ℂ) (S : Finset (Primes M)) (x : M) :
    ‖sifted f S x‖ ≤ ‖f x‖ := by
  classical
  simp only [sifted]
  split_ifs <;> simp

omit [IsCancelMulZero M] [Subsingleton Mˣ] in
theorem sifted_summable (f : M →*₀ ℂ) (hf : Summable (fun x => ‖f x‖))
    (S : Finset (Primes M)) : Summable (sifted f S) :=
  (hf.of_nonneg_of_le (fun _ => norm_nonneg _) (sifted_norm_le f S)).of_norm

theorem sifted_mul (f : M →*₀ ℂ) (S : Finset (Primes M))
    (p : Primes M) (hp : p ∉ S) (x : M) :
    sifted f S (p.val * x) = f p.val * sifted f S x := by
  classical
  have he : (∀ q ∈ S, ¬ q.val ∣ p.val * x) ↔ ∀ q ∈ S, ¬ q.val ∣ x := by
    apply forall₂_congr
    intro q hq
    have hn : ¬ q.val ∣ p.val := by
      intro hd
      have hqp : q = p := Subtype.ext ((prime_dvd_prime_iff_eq q.property p.property).mp hd)
      exact hp (hqp ▸ hq)
    rw [q.property.dvd_mul, not_or, and_iff_right hn]
  simp only [sifted, he, map_mul]
  split_ifs <;> simp

theorem sifted_insert (f : M →*₀ ℂ) (hf : Summable (fun x => ‖f x‖))
    (S : Finset (Primes M)) (p : Primes M) (hp : p ∉ S) :
    (∑' x, sifted f (insert p S) x) = (1 - f p.val) * ∑' x, sifted f S x := by
  classical
  let d : M → ℂ := fun x => if p.val ∣ x then sifted f S x else 0
  have hd : Summable d := by
    apply hf.of_norm_bounded
    intro x
    dsimp [d]
    split_ifs
    · exact sifted_norm_le f S x
    · simp
  have hreindex : (∑' x, d x) = f p.val * ∑' x, sifted f S x := by
    have hi : Function.Injective (fun x : M => p.val * x) := mul_right_injective₀ p.property.ne_zero
    rw [← hi.tsum_eq (f := d) (by
      intro x hx
      have hpx : p.val ∣ x := by
        by_contra h
        exact hx (by simp [d, h])
      obtain ⟨y, rfl⟩ := hpx
      exact ⟨y, rfl⟩)]
    simp only [d, dvd_mul_right, ↓reduceIte, sifted_mul f S p hp]
    exact tsum_mul_left
  have hsplit : (fun x => sifted f (insert p S) x + d x) = sifted f S := by
    funext x
    simp only [sifted, Finset.mem_insert, forall_eq_or_imp, d]
    by_cases h : p.val ∣ x <;> simp [h]
  have h := congrArg (fun g : M → ℂ => ∑' x, g x) hsplit
  change (∑' x, (sifted f (insert p S) x + d x)) = ∑' x, sifted f S x at h
  rw [Summable.tsum_add (sifted_summable f hf (insert p S)) hd, hreindex] at h
  linear_combination h

theorem finite_product (f : M →*₀ ℂ) (hf : Summable (fun x => ‖f x‖))
    (S : Finset (Primes M)) :
    (∑' x, f x) * (∏ p ∈ S, (1 - f p.val)) = ∑' x, sifted f S x := by
  classical
  induction S using Finset.induction with
  | empty => simp [sifted]
  | insert p S hp ih =>
    rw [Finset.prod_insert hp, sifted_insert f hf S p hp, ← ih]
    ring

omit [IsCancelMulZero M] [Subsingleton Mˣ] in
theorem sifted_limit (f : M →*₀ ℂ) (hf : Summable (fun x => ‖f x‖))
    (hprime : ∀ x : M, x ≠ 0 → x ≠ 1 → ∃ p : Primes M, p.val ∣ x) :
    Tendsto (fun S : Finset (Primes M) => ∑' x, sifted f S x) atTop (𝓝 1) := by
  classical
  have hpoint (x : M) : Tendsto (fun S : Finset (Primes M) => sifted f S x)
      atTop (𝓝 (if x = 1 then (1 : ℂ) else 0)) := by
    by_cases hx : x = 1
    · subst x
      have he (S : Finset (Primes M)) : sifted f S 1 = 1 := by
        simp only [sifted, map_one]
        rw [if_pos]
        exact fun p _ hp => p.property.not_unit (isUnit_of_dvd_one hp)
      simpa only [he, ↓reduceIte] using (tendsto_const_nhds :
        Tendsto (fun _ : Finset (Primes M) => (1 : ℂ)) atTop (𝓝 1))
    · by_cases hx0 : x = 0
      · subst x
        have he (S : Finset (Primes M)) : sifted f S 0 = 0 := by simp [sifted]
        simpa only [he, if_neg hx] using (tendsto_const_nhds :
          Tendsto (fun _ : Finset (Primes M) => (0 : ℂ)) atTop (𝓝 0))
      · obtain ⟨p, hp⟩ := hprime x hx0 hx
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ({p} : Finset (Primes M))] with S hS
        have hn : ¬ ∀ q ∈ S, ¬ q.val ∣ x := by
          intro h
          exact h p (hS (by simp)) hp
        simp only [sifted, if_neg hn, if_neg hx]
  have h := tendsto_tsum_of_dominated_convergence hf hpoint
    (Filter.Eventually.of_forall (fun S x => sifted_norm_le f S x))
  simpa using h

theorem sum_mul_product (f : M →*₀ ℂ) (hf : Summable (fun x => ‖f x‖))
    (hprime : ∀ x : M, x ≠ 0 → x ≠ 1 → ∃ p : Primes M, p.val ∣ x) :
    (∑' x, f x) * (∏' p : Primes M, (1 - f p.val)) = 1 := by
  have hm : Multipliable (fun p : Primes M => 1 - f p.val) := by
    simpa using multipliable_one_add_of_summable (by simpa using hf.subtype (fun p => Prime p) :
      Summable (fun p : Primes M => ‖-f p.val‖))
  have h := (tendsto_const_nhds (x := ∑' x, f x)).mul hm.hasProd
  have he : (fun S : Finset (Primes M) => (∑' x, f x) * ∏ p ∈ S, (1 - f p.val)) =
      fun S => ∑' x, sifted f S x := funext (finite_product f hf)
  change Tendsto (fun S : Finset (Primes M) => (∑' x, f x) * ∏ p ∈ S, (1 - f p.val)) _ _ at h
  rw [he] at h
  exact tendsto_nhds_unique h (sifted_limit f hf hprime)

end Cubic.PoissonSummation.IdealEulerSieve
