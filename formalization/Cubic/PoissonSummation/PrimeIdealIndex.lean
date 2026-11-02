import Cubic.PoissonSummation.DedekindZetaEulerProduct
import Mathlib.RingTheory.Ideal.Int

/-!
# Indexing actual prime ideals by the rational prime below them

The fibers are identified with mathlib's `Ideal.primesOver`, so subsequent
Euler-factor computations use its genuine residue degrees and prime counts.
-/

noncomputable section

namespace Cubic.PoissonSummation.PrimeIdealIndex

open Ideal NumberField DedekindZetaEulerProduct

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalPrime (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p : ℤ)}

def below (P : PrimeIdeals K) : Nat.Primes := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  letI : NeZero P.val := ⟨P.property.ne_zero⟩
  exact ⟨Ideal.absNorm (P.val.under ℤ), Nat.absNorm_under_prime P.val⟩

theorem liesOver_below (P : PrimeIdeals K) : P.val.LiesOver (rationalPrime (below K P)) :=
  Int.liesOver_span_absNorm P.val

theorem below_eq (P : PrimeIdeals K) (p : Nat.Primes)
    [P.val.LiesOver (rationalPrime p)] : below K P = p := by
  apply Subtype.ext
  change Ideal.absNorm (P.val.under ℤ) = (p : ℕ)
  rw [← Ideal.over_def P.val (rationalPrime p)]
  simp [rationalPrime, Ideal.absNorm_span_singleton]

def fiberEquiv (p : Nat.Primes) :
    {P : PrimeIdeals K // below K P = p} ≃ (rationalPrime p).primesOver (𝓞 K) where
  toFun P := ⟨P.val.val, Ideal.isPrime_of_prime P.val.property, by
    simpa only [P.property] using liesOver_below K P.val⟩
  invFun Q := by
    have hp : rationalPrime p ≠ ⊥ := by simpa using p.property.ne_zero
    let P : PrimeIdeals K := ⟨Q.val, Ideal.prime_of_mem_primesOver hp Q.property⟩
    letI : P.val.LiesOver (rationalPrime p) := Q.property.2
    exact ⟨P, below_eq K P p⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiber_product (p : Nat.Primes) (f : Ideal (𝓞 K) → ℂ) :
    (∏' P : (below K) ⁻¹' {p}, f P.val.val) =
      ∏' Q : (rationalPrime p).primesOver (𝓞 K), f Q.val :=
  (fiberEquiv K p).tprod_eq (fun Q => f Q.val)

theorem grouped_euler_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏' Q : (rationalPrime p).primesOver (𝓞 K),
        (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  have h := ((Equiv.sigmaFiberEquiv (below K)).hasProd_iff).mpr (euler_hasProd K s hs)
  have hg : HasProd (fun p : Nat.Primes =>
      ∏' P : (below K) ⁻¹' {p}, (1 - (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
    apply h.sigma
    intro p
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    letI : Finite ((below K) ⁻¹' {p}) := Finite.of_equiv
      ((rationalPrime p).primesOver (𝓞 K)) (fiberEquiv K p).symm
    change HasProd (fun P : (below K) ⁻¹' {p} => (1 - (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹)
      (∏' P : (below K) ⁻¹' {p}, (1 - (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹)
    exact Multipliable.of_finite.hasProd
  have he : (fun p : Nat.Primes =>
      ∏' P : (below K) ⁻¹' {p}, (1 - (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹) =
      fun p => ∏' Q : (rationalPrime p).primesOver (𝓞 K),
        (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹ :=
    funext (fun p => fiber_product K p (fun I => (1 - (Ideal.absNorm I : ℂ) ^ (-s))⁻¹))
  rw [he] at hg
  exact hg

end Cubic.PoissonSummation.PrimeIdealIndex
