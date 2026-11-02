import Cubic.BoxAsymptotic.AngularRamified
import Cubic.BoxAsymptotic.AngularSeriesConvergence
import CubicTargets.BoxAsymptotic.AngularSeries

/-! Summation of the local angular coefficient table: the primary-element version
of `eq:Fk`, with absolute convergence proved before reindexing the double sum. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularLocalSeries

open Complex CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData
open Cubic.BoxAsymptotic.AngularRamified Cubic.BoxAsymptotic.ZeroModeSeries

def y (k : ℤ) (s : ℂ) : ℂ := ramifiedPhase k * (3 : ℂ) ^ (-s)

def localFactor (k : ℤ) (s : ℂ) : ℂ :=
  (1 / 3) * (1 + y k s + 3 * (if 6 ∣ k then 1 else 0) * y k s ^ 2 / (1 - y k s))

def localTerm (k : ℤ) (s : ℂ) (e : ℕ) : ℂ :=
  localWeight k e * ((3 : ℂ) ^ (-s)) ^ e

theorem norm_y_lt_one (k : ℤ) (s : ℂ) (hs : 1 < s.re) : ‖y k s‖ < 1 := by
  rw [y, norm_mul, norm_ramifiedPhase, one_mul]
  exact (Complex.norm_prime_cpow_le_one_half ⟨3, Nat.prime_three⟩ hs).trans_lt (by norm_num)

theorem one_sub_y_ne_zero (k : ℤ) (s : ℂ) (hs : 1 < s.re) : 1 - y k s ≠ 0 := by
  intro h
  have hy : y k s = 1 := (sub_eq_zero.mp h).symm
  have hnorm := norm_y_lt_one k s hs
  simp [hy] at hnorm

theorem localTerm_eq (k : ℤ) (s : ℂ) (e : ℕ) :
    localTerm k s e =
      (if e < 2 then (1 / 3 : ℂ) else if 6 ∣ k then 1 else 0) * y k s ^ e := by
  simp only [localTerm, localWeight, y, mul_pow]
  ring

set_option maxHeartbeats 800000 in
theorem local_hasSum (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    HasSum (localTerm k s) (localFactor k s) := by
  let c : ℂ := if 6 ∣ k then 1 else 0
  have htail : HasSum (fun e => localTerm k s (e + 1 + 1))
      (c * y k s ^ 2 / (1 - y k s)) := by
    convert (hasSum_geometric_of_norm_lt_one (norm_y_lt_one k s hs)).mul_left
      (c * y k s ^ 2) using 1
    · funext e
      rw [localTerm_eq, if_neg (show ¬ e + 1 + 1 < 2 by omega)]
      dsimp [c]
      ring
  have h := htail.zero_add.zero_add
  convert h using 1
  simp only [localTerm_eq, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    if_true, Nat.zero_add, pow_zero, pow_one, mul_one]
  dsimp [localFactor, c]
  field_simp [one_sub_y_ne_zero k s hs]
  ring

theorem away_hasSum
    {k : ℤ} (hk : Even k) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun m : AwayThree => awayCoefficient k m.1 * (m.1 : ℂ) ^ (-s))
      (awaySeries k s) := by
  have hsupport : Function.support (LSeries.term (awayCoefficient k) s) ⊆
      {m : ℕ | ¬ 3 ∣ m} := by
    intro m hm hd
    apply hm
    simp [LSeries.term_def, awayCoefficient, hd]
  have hfull := (AngularSeriesConvergence.away_summable hk s hs).hasSum
  have hh := (hasSum_subtype_iff_of_support_subset hsupport).mpr hfull
  convert hh using 1
  funext m
  exact (LSeries.term_def₀ (f := awayCoefficient k) (by simp [awayCoefficient]) s m.1).symm

theorem term_factor {k : ℤ} (hk : Even k) (s : ℂ) (p : ℕ × AwayThree) :
    localTerm k s p.1 * (awayCoefficient k p.2.1 * (p.2.1 : ℂ) ^ (-s)) =
      LSeries.term (coefficient k) s (decomposition p).1 := by
  rw [LSeries.term_of_ne_zero (decomposition p).2, div_eq_mul_inv, ← Complex.cpow_neg]
  change _ = coefficient k (3 ^ p.1 * p.2.1) * ((3 ^ p.1 * p.2.1 : ℕ) : ℂ) ^ (-s)
  rw [coefficient_power _ _ (away_pos p.2) p.2.2 hk, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, Cubic.PoissonSummation.HeightCountingEulerProduct.nat_pow_cpow]
  dsimp [localTerm]
  ring

theorem series_eq
    {k : ℤ} (hk : Even k) (s : ℂ) (hs : 1 < s.re) :
    series k s = localFactor k s * awaySeries k s := by
  have hL := local_hasSum k s hs
  have hA := away_hasSum hk s hs
  have hnorm := summable_mul_of_summable_norm (f := localTerm k s)
    (g := fun m : AwayThree => awayCoefficient k m.1 * (m.1 : ℂ) ^ (-s))
    hL.summable.norm hA.summable.norm
  have hprod := hL.mul hA hnorm
  have heq : (fun p : ℕ × AwayThree => localTerm k s p.1 *
      (awayCoefficient k p.2.1 * (p.2.1 : ℂ) ^ (-s))) =
      (fun p => LSeries.term (coefficient k) s (decomposition p).1) := by
    funext p
    exact term_factor hk s p
  rw [heq] at hprod
  have hpos := (decomposition.hasSum_iff
    (f := fun n : {n : ℕ // n ≠ 0} => LSeries.term (coefficient k) s n.1)).mp hprod
  have hsupp : Function.support (LSeries.term (coefficient k) s) ⊆ {n : ℕ | n ≠ 0} := by
    intro n hn h0; subst n; simp at hn
  exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hpos).tsum_eq

/-- Supporting coefficient identity for `eq:Fk`. -/
theorem coefficient_claim : AngularCoefficientClaim :=
  fun _ hk e M hM h3 => coefficient_power e M hM h3 hk

/-- `eq:Fk` in the primary-element formulation, retaining the original Fourier sign.
The Hecke ideal-series interpretation of `D_k` is not asserted here. -/
theorem local_series_claim
    :
    AngularLocalSeriesClaim := by
  refine ⟨AngularSeriesConvergence.summable, fun _ hk s =>
    AngularSeriesConvergence.series_odd hk s, fun k hk s hs => ?_⟩
  refine ⟨AngularSeriesConvergence.away_summable hk s hs, ?_⟩
  simpa only [localFactor, y, ramifiedPhase_even hk] using series_eq hk s hs

end Cubic.BoxAsymptotic.AngularLocalSeries
