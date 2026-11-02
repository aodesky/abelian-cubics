import Cubic.BoxAsymptotic.IdealCharacterEulerProduct
import Cubic.BoxAsymptotic.HeckePrimitiveCharacters
import Cubic.PoissonSummation.QuadraticIdealSplitting

/-! Removing the actual prime above three from the primitive Hecke series.
The comparison is proved from the two convergent Euler products, including
the case in which the primitive character already vanishes at that prime. -/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeOmitThree

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.PoissonSummation.DedekindZetaEulerProduct
open Cubic.PoissonSummation.QuadraticIdealSplitting
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.HeckeSeriesConvergence

def primeAbove : Ideal Integers := (Set.ncard_eq_one.mp ramified_count).choose

theorem primesOver_three : (rationalPrime primeThree).primesOver Integers = {primeAbove} :=
  (Set.ncard_eq_one.mp ramified_count).choose_spec

theorem primeAbove_mem : primeAbove ∈ (rationalPrime primeThree).primesOver Integers := by
  rw [primesOver_three]; exact Set.mem_singleton _

def primeIndex : PrimeIdeals E :=
  ⟨primeAbove, Ideal.prime_of_mem_primesOver (by norm_num [rationalPrime, primeThree])
    primeAbove_mem⟩

theorem primeAbove_norm : Ideal.absNorm primeAbove = 3 := by
  letI := primeAbove_mem.1
  letI := primeAbove_mem.2
  exact ramified_norm _

theorem prime_eq_of_three_dvd (P : PrimeIdeals E) (h : 3 ∣ Ideal.absNorm P.val) :
    P = primeIndex := by
  let p := Cubic.PoissonSummation.PrimeIdealIndex.below E P
  letI := Ideal.isPrime_of_prime P.property
  letI := Cubic.PoissonSummation.PrimeIdealIndex.liesOver_below E P
  have hn := Ideal.absNorm_eq_pow_inertiaDeg' P.val p.property
  have hp : p = primeThree := by
    apply Subtype.ext
    have hd := Nat.prime_three.dvd_of_dvd_pow (hn ▸ h)
    exact (p.property.dvd_iff_eq (by norm_num : 3 ≠ 1)).mp hd
  have hm : P.val ∈ (rationalPrime primeThree).primesOver Integers := by
    refine ⟨inferInstance, ?_⟩
    simpa only [← hp] using
      (Cubic.PoissonSummation.PrimeIdealIndex.liesOver_below E P)
  rw [primesOver_three, Set.mem_singleton_iff] at hm
  exact Subtype.ext hm

theorem primitive_norm (k : ℤ) (I : Ideal Integers) : ‖primitiveHom k I‖ ≤ 1 := by
  rw [primitiveHom_eq]
  exact norm_primitivePsi_le k I

theorem agree_away (k : ℤ) {I : Ideal Integers} (hI : ¬ 3 ∣ Ideal.absNorm I) :
    primitiveHom k I = psi k I := by
  rw [primitiveHom_eq, primitivePsi]
  split_ifs
  · exact generatorPhase_away k hI
  · rfl

def factor (k : ℤ) (s : ℂ) : ℂ :=
  1 - primitiveHom k primeAbove * (3 : ℂ) ^ (-s)

theorem factor_entire (k : ℤ) : Differentiable ℂ (factor k) := by
  exact (differentiable_const _).sub ((differentiable_const _).mul
    (differentiable_id.neg.const_cpow (.inl (by norm_num : (3 : ℂ) ≠ 0))))

theorem factor_bound (k : ℤ) (s : ℂ) (hs : 0 ≤ s.re) : ‖factor k s‖ ≤ 2 := by
  have hp : ‖(3 : ℂ) ^ (-s)‖ ≤ 1 := by
    change ‖((3 : ℝ) : ℂ) ^ (-s)‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hs)
  have hm : ‖primitiveHom k primeAbove * (3 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (primitive_norm k _)).trans hp
  have ht := norm_sub_le (1 : ℂ) (primitiveHom k primeAbove * (3 : ℂ) ^ (-s))
  rw [norm_one] at ht
  exact ht.trans (by linarith)

theorem series_eq (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    heckeSeries k s = factor k s *
      LSeries (coefficient (primitiveHom k)) s := by
  classical
  let f := fun P : PrimeIdeals E =>
    (1 - primitiveHom k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹
  let g := fun P : PrimeIdeals E =>
    (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹
  have hf := IdealCharacterEulerProduct.euler_hasProd (primitiveHom k) (primitive_norm k) s hs
  have hg := IdealCharacterEulerProduct.euler_hasProd
    (HeckeFiniteCharacter.psiHom k) (norm_psi_le k) s hs
  have hu : Function.update f primeIndex 1 = g := by
    funext P
    by_cases hP : P = primeIndex
    · subst P
      simp [f, g, primeIndex, psi, primeAbove_norm]
    · rw [Function.update_of_ne hP]
      dsimp only [f, g]
      rw [agree_away k (fun h => hP (prime_eq_of_three_dvd P h))]
  change HasProd g (heckeSeries k s) at hg
  rw [← hu] at hg
  have he := hf.update' primeIndex 1 hg
  change LSeries (coefficient (primitiveHom k)) s * 1 = heckeSeries k s * f primeIndex at he
  have hn : factor k s ≠ 0 := by
    have hc : ‖primitiveHom k primeAbove * (3 : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      have hp : ‖(3 : ℂ) ^ (-s)‖ < 1 := by
        change ‖((3 : ℝ) : ℂ) ^ (-s)‖ < 1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3)]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp only [Complex.neg_re]; linarith)
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (primitive_norm k _)) hp
    intro h
    have hv := (sub_eq_zero.mp h).symm
    rw [hv, norm_one] at hc
    exact (lt_irrefl 1) hc
  have hv : f primeIndex = (factor k s)⁻¹ := by simp only [f, primeIndex, primeAbove_norm, factor, Nat.cast_ofNat]
  rw [mul_one, hv] at he
  rw [he, ← mul_assoc, mul_comm (factor k s), mul_assoc, mul_inv_cancel₀ hn, mul_one]

end Cubic.BoxAsymptotic.HeckeOmitThree
