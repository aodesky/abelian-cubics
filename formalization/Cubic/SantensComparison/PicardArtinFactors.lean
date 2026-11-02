import Cubic.SantensComparison.PicardLattices
import Cubic.PoissonSummation.QuadraticDedekindFactorization
import Cubic.PoissonSummation.QuadraticDedekindResidue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The Artin factors of the permutation lattice obtained from the actual
open Picard quotient. Frobenius is the identity at split primes and the
coordinate transposition at inert primes. At three, inertia invariants form
the diagonal line. Comparison is with the genuine prime-ideal Euler factors. -/

noncomputable section

namespace Cubic.SantensComparison.PicardArtinFactors

open FanData PicardLattices
open Cubic.PoissonSummation FiniteEulerProduct
open Cubic.QuadraticCorrespondence.CyclotomicField

def swapMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

theorem quotient_action (d : Fin 4 → ℤ) :
    swapMatrix.mulVec ![((openProjection d).1 : ℂ), ((openProjection d).2 : ℂ)] =
      ![((openProjection (conjugateOpenDivisor d)).1 : ℂ),
        ((openProjection (conjugateOpenDivisor d)).2 : ℂ)] := by
  have h := open_picard_conjugation d
  simp only [open_picard_mk] at h
  rw [h]
  ext i
  fin_cases i <;> simp [swapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem inertia_invariants (m : ℂ × ℂ) : (m.2,m.1) = m ↔ ∃ a : ℂ, m = (a,a) := by
  constructor
  · intro h
    exact ⟨m.1, Prod.ext rfl (congrArg Prod.fst h)⟩
  · rintro ⟨a,rfl⟩
    rfl

def splitPolynomial (t : ℂ) : ℂ := Matrix.det (1 - t • (1 : Matrix (Fin 2) (Fin 2) ℂ))
def inertPolynomial (t : ℂ) : ℂ := Matrix.det (1 - t • swapMatrix)
def ramifiedPolynomial (t : ℂ) : ℂ :=
  Matrix.det (1 - t • (1 : Matrix (Fin 1) (Fin 1) ℂ))

theorem split_polynomial (t : ℂ) : splitPolynomial t = (1-t)^2 := by
  simp [splitPolynomial, Matrix.det_fin_two, pow_two]

theorem inert_polynomial (t : ℂ) : inertPolynomial t = 1-t^2 := by
  simp [inertPolynomial, swapMatrix, Matrix.det_fin_two, pow_two]

theorem ramified_polynomial (t : ℂ) : ramifiedPolynomial t = 1-t := by
  simp [ramifiedPolynomial, Matrix.det_unique]

/-- The Euler factor is the reciprocal characteristic determinant on inertia
invariants, for the permutation action proved above. -/
def localFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  if p = primeThree then (ramifiedPolynomial ((p : ℂ)^(-s)))⁻¹
  else if (p : ℕ) % 3 = 1 then (splitPolynomial ((p : ℂ)^(-s)))⁻¹
  else (inertPolynomial ((p : ℂ)^(-s)))⁻¹

def artinL (s : ℂ) : ℂ := ∏' p : Nat.Primes, localFactor p s

theorem local_factor_eq (p : Nat.Primes) (s : ℂ) :
    localFactor p s = QuadraticDedekindFactorization.localFactor p s := by
  by_cases h3 : p = primeThree
  · subst p
    rw [localFactor, if_pos rfl, ramified_polynomial,
      QuadraticDedekindFactorization.ramified_factor]
    rfl
  rw [localFactor, if_neg h3]
  by_cases h1 : (p : ℕ) % 3 = 1
  · rw [if_pos h1, split_polynomial, QuadraticDedekindFactorization.split_factor ⟨p,h1⟩]
    simp only [inv_pow]
  · have h0 : (p : ℕ) % 3 ≠ 0 := by
      intro h
      have he : (p : ℕ) = 3 := (p.2.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h)
      exact h3 (Subtype.ext he)
    have h2 : (p : ℕ) % 3 = 2 := by omega
    rw [if_neg h1, inert_polynomial, QuadraticDedekindFactorization.inert_factor ⟨p,h2⟩]

theorem artin_eq_dedekind (s : ℂ) (hs : 1 < s.re) :
    artinL s = NumberField.dedekindZeta E s := by
  unfold artinL
  simp_rw [local_factor_eq]
  exact (PrimeIdealIndex.grouped_euler_hasProd E s hs).tprod_eq

theorem residue_limit : Filter.Tendsto
    (fun s : ℝ => ((s-1 : ℝ) : ℂ) * artinL s)
    (nhdsWithin 1 (Set.Ioi 1))
    (nhds ((Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)))) := by
  apply QuadraticDedekindResidue.residue_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [artin_eq_dedekind _ (by simpa using hs)]

end Cubic.SantensComparison.PicardArtinFactors
