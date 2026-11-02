import CubicTargets.BoxAsymptotic.AngularEulerProduct
import Cubic.BoxAsymptotic.AngularEulerSeries
import Cubic.BoxAsymptotic.HeckeRationalEulerFactors
import Cubic.BoxAsymptotic.AngularCorrectionBounds

/-! `eq:Dk`: comparison of the Euler factors of the independently defined
cube-norm series with the two actual Hecke series and the correction product.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularEulerProduct

open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.AngularCorrectionProduct Cubic.BoxAsymptotic.AngularCorrectionBounds
open Cubic.BoxAsymptotic.HeckeRationalEulerFactors
open Cubic.BoxAsymptotic.HeckePrimeFactors
open Cubic.BoxAsymptotic.AngularEulerSeries

theorem cancel_pair (A B C D N : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) :
    N / (C * D) = A⁻¹ * B⁻¹ * (C⁻¹ * D⁻¹) * (N * (A * B)) := by
  rw [div_eq_mul_inv, mul_inv]
  calc
    _ = (A⁻¹ * A) * (B⁻¹ * B) * (N * (C⁻¹ * D⁻¹)) := by
      rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hB, one_mul, one_mul]
    _ = _ := by ring

theorem cpow_multiple (p : Nat.Primes) (s : ℂ) (j : ℕ) :
    (p : ℂ) ^ (-((j : ℂ) * s)) = ((p : ℂ) ^ (-s)) ^ j := by
  rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]

theorem split_comparison (k : ℤ) (p : SplitPrimes) (s : ℂ) (hs : 1 < s.re) :
    (∑' j, term k s ((p.1 : ℕ) ^ j)) =
      factor k p.1 s * factor (3 * k) p.1 s * primeFactor k p.1 s := by
  rw [(split_hasSum k p s hs).tsum_eq, split_factor, split_factor, primeFactor_split]
  have hphase : splitPhase (3 * k) p = splitPhase k p ^ 3 :=
    psi_three_mul k (splitPrime p)
  rw [hphase, split, quadraticCoefficient, cubicCoefficient]
  have hp2 := cpow_multiple p.1 s 2
  have hp3 := cpow_multiple p.1 s 3
  norm_num only [Nat.cast_ofNat] at hp2 hp3
  rw [hp2, hp3]
  simp only [← inv_pow]
  set a := splitPhase k p
  set x := (p.1 : ℂ) ^ (-s)
  have ha : ‖a‖ = 1 := norm_splitPhase k p
  have hane : a ≠ 0 := by intro h; simp [h] at ha
  have hx : ‖x‖ < 1 := (Complex.norm_prime_cpow_le_one_half p.1 hs).trans_lt (by norm_num)
  have h1 : 1 - a * x ≠ 0 := AngularEulerLocal.one_sub_ne_zero
    (by simpa only [norm_mul, ha, one_mul] using hx)
  have h2 : 1 - a⁻¹ * x ≠ 0 := AngularEulerLocal.one_sub_ne_zero
    (by simpa only [norm_mul, norm_inv, ha, inv_one, one_mul] using hx)
  rw [← AngularEulerLocal.correction_identity (mul_inv_cancel₀ hane)]
  exact cancel_pair _ _ _ _ _ h1 h2

theorem inert_comparison {k : ℤ} (hk : Even k) (p : InertPrimes) (s : ℂ) (hs : 1 < s.re) :
    (∑' j, term k s ((p.1 : ℕ) ^ j)) =
      factor k p.1 s * factor (3 * k) p.1 s * primeFactor k p.1 s := by
  rw [(inert_hasSum hk p s hs).tsum_eq, inert_factor hk, inert_factor (hk.mul_left 3),
    primeFactor_inert]
  change _ = _ * _ * (1 - (p.1 : ℂ) ^ (-(2 * s)))
  have hp2 := cpow_multiple p.1 s 2
  norm_num only [Nat.cast_ofNat] at hp2
  rw [hp2]
  have hx : ‖((p.1 : ℂ) ^ (-s)) ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := Complex.norm_prime_cpow_le_one_half p.1 hs
    have := norm_nonneg ((p.1 : ℂ) ^ (-s))
    nlinarith
  rw [mul_assoc, inv_mul_cancel₀ (AngularEulerLocal.one_sub_ne_zero hx), mul_one]

theorem local_comparison {k : ℤ} (hk : Even k) (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    (∑' j, term k s ((p : ℕ) ^ j)) = factor k p s * factor (3 * k) p s * primeFactor k p s := by
  by_cases h1 : (p : ℕ) % 3 = 1
  · exact split_comparison k ⟨p, h1⟩ s hs
  by_cases h2 : (p : ℕ) % 3 = 2
  · exact inert_comparison hk ⟨p, h2⟩ s hs
  have h0 : (p : ℕ) % 3 = 0 := by omega
  have h3 : p = primeThree := by
    apply Subtype.ext
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three p.2).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  subst p
  rw [three_factor, three_factor, one_mul, one_mul]
  simpa only [primeFactor, primeThree, Nat.reduceMod, ↓reduceDIte] using (three_hasSum k s).tsum_eq

/-- The paper's identity for `D_k`, on its half-plane of absolute convergence.
Absolute convergence follows from the fourfold divisor majorant through
`AngularSeriesConvergence.away_summable`. -/
theorem «eq:Dk» : CubicTargets.BoxAsymptotic.AngularEulerProductClaim := by
  intro k hk s hs
  have hD := euler_hasProd hk s hs
  have hL := ((factor_hasProd k s hs).mul (factor_hasProd (3 * k) s hs)).mul
    (value_hasProd k s (by linarith))
  apply hD.unique
  simpa only [local_comparison hk _ s hs] using hL

end Cubic.BoxAsymptotic.AngularEulerProduct
