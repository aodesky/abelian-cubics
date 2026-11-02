import Cubic.BoxAsymptotic.HeckeFiniteCharacter
import Cubic.BoxAsymptotic.HeckeSeriesConvergence
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! Multiplication identifies the norm fibers at coprime integers.  This is the
arithmetic reason that the character sums, and their cube-norm subsequence,
have Euler products.  The fibers here consist of actual integral ideals.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.IdealNormFibers

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.HeckeFiniteCharacter

abbrev Fiber (n : ℕ) := {I : Ideal Integers // Ideal.absNorm I = n}

theorem norm_span_nat (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : Integers)}) = n ^ 2 := by
  have he : (n : Integers) = coord (n, 0) := by simp [coord]
  rw [he, Ideal.absNorm_span_singleton, norm_coord]
  simp

theorem relPrime_of_coprime_norm {I J : Ideal Integers}
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) : IsRelPrime I J := by
  intro D hDI hDJ
  apply Ideal.isUnit_iff.mpr
  apply Ideal.absNorm_eq_one_iff.mp
  exact Nat.dvd_one.mp (h ▸ Nat.dvd_gcd (map_dvd Ideal.absNorm hDI)
    (map_dvd Ideal.absNorm hDJ))

theorem exists_mul {m n : ℕ} (hmn : m.Coprime n)
    {I : Ideal Integers} (hI : Ideal.absNorm I = m * n) :
    ∃ J K : Ideal Integers, Ideal.absNorm J = m ∧ Ideal.absNorm K = n ∧ J * K = I := by
  have hd : I ∣ Ideal.span {(m : Integers)} * Ideal.span {(n : Integers)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hI]
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_absNorm_le I)
  obtain ⟨J, K, hJ, hK, he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have hJN : Ideal.absNorm J ∣ m ^ 2 := by
    simpa only [norm_span_nat] using map_dvd Ideal.absNorm hJ
  have hKN : Ideal.absNorm K ∣ n ^ 2 := by
    simpa only [norm_span_nat] using map_dvd Ideal.absNorm hK
  have hprod : Ideal.absNorm J * Ideal.absNorm K = m * n := by
    rw [← map_mul, ← he, hI]
  have hJm : Ideal.absNorm J ∣ m :=
    (hmn.pow_left 2 |>.of_dvd_left hJN).dvd_of_dvd_mul_right
      (hprod ▸ dvd_mul_right (Ideal.absNorm J) (Ideal.absNorm K))
  have hKn : Ideal.absNorm K ∣ n :=
    (hmn.pow_right 2 |>.of_dvd_right hKN).symm.dvd_of_dvd_mul_left
      (hprod ▸ dvd_mul_left (Ideal.absNorm K) (Ideal.absNorm J))
  have hmJ : m ∣ Ideal.absNorm J :=
    (hmn.pow_right 2 |>.of_dvd_right hKN).dvd_of_dvd_mul_right
      (hprod.symm ▸ dvd_mul_right m n)
  have hnK : n ∣ Ideal.absNorm K :=
    (hmn.pow_left 2 |>.of_dvd_left hJN).symm.dvd_of_dvd_mul_left
      (hprod.symm ▸ dvd_mul_left n m)
  exact ⟨J, K, Nat.dvd_antisymm hJm hmJ, Nat.dvd_antisymm hKn hnK, he.symm⟩

def mul (m n : ℕ) : Fiber m × Fiber n → Fiber (m * n) := fun x =>
  ⟨x.1.val * x.2.val, by rw [map_mul, x.1.property, x.2.property]⟩

theorem mul_injective {m n : ℕ} (hmn : m.Coprime n) : Function.Injective (mul m n) := by
  rintro ⟨I, J⟩ ⟨I', J'⟩ he
  have he' : I.val * J.val = I'.val * J'.val := congrArg Subtype.val he
  have hc (A : Fiber m) (B : Fiber n) : IsRelPrime A.val B.val :=
    relPrime_of_coprime_norm (by simpa only [A.property, B.property] using hmn)
  have hI : I = I' := by
    apply Subtype.ext
    apply le_antisymm <;> apply Ideal.dvd_iff_le.mp
    · exact (hc I' J).dvd_of_dvd_mul_right
        (he'.symm ▸ dvd_mul_right I'.val J'.val)
    · exact (hc I J').dvd_of_dvd_mul_right
        (he' ▸ dvd_mul_right I.val J.val)
  have hJ : J = J' := by
    apply Subtype.ext
    apply le_antisymm <;> apply Ideal.dvd_iff_le.mp
    · exact (hc I J').symm.dvd_of_dvd_mul_left
        (he'.symm ▸ dvd_mul_left J'.val I'.val)
    · exact (hc I' J).symm.dvd_of_dvd_mul_left
        (he' ▸ dvd_mul_left J.val I.val)
  exact Prod.ext hI hJ

theorem mul_surjective {m n : ℕ} (hmn : m.Coprime n) : Function.Surjective (mul m n) := by
  intro I
  obtain ⟨J, K, hJ, hK, he⟩ := exists_mul hmn I.property
  exact ⟨(⟨J, hJ⟩, ⟨K, hK⟩), Subtype.ext he⟩

def mulEquiv {m n : ℕ} (hmn : m.Coprime n) : Fiber m × Fiber n ≃ Fiber (m * n) :=
  Equiv.ofBijective (mul m n) ⟨mul_injective hmn, mul_surjective hmn⟩

theorem coefficient_mul (χ : Ideal Integers →*₀ ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    HeckeSeriesConvergence.coefficient χ (m * n) =
      HeckeSeriesConvergence.coefficient χ m * HeckeSeriesConvergence.coefficient χ n := by
  classical
  letI : Fintype (Fiber m) := (Ideal.finite_setOf_absNorm_eq m).fintype
  letI : Fintype (Fiber n) := (Ideal.finite_setOf_absNorm_eq n).fintype
  have hf (q : ℕ) : HeckeSeriesConvergence.coefficient χ q =
      ∑ᶠ I : Fiber q, χ I.val := (finsum_subtype_eq_finsum_cond _).symm
  rw [hf, hf, hf, ← finsum_comp_equiv (mulEquiv hmn)]
  simp only [mulEquiv, Equiv.ofBijective_apply, mul, map_mul,
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem coefficient_one (χ : Ideal Integers →*₀ ℂ) :
    HeckeSeriesConvergence.coefficient χ 1 = 1 := by
  have he : {I : Ideal Integers | Ideal.absNorm I = 1} = {1} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  rw [HeckeSeriesConvergence.coefficient, he]
  simpa only [finsum_mem_singleton] using map_one χ

theorem cube_coefficient (k : ℤ) (n : ℕ) :
    idealCoefficient k n = HeckeSeriesConvergence.coefficient (psi k) (n ^ 3) := by
  classical
  by_cases hn : 3 ∣ n
  · rw [idealCoefficient, if_pos hn, HeckeSeriesConvergence.coefficient]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro I
    by_cases hI : Ideal.absNorm I = n ^ 3
    · simp [hI, psi, dvd_pow hn (by norm_num : 3 ≠ 0)]
    · simp [hI]
  · simp only [idealCoefficient, hn, if_false, HeckeSeriesConvergence.coefficient,
      cubeNormIdeals]

theorem idealCoefficient_mul (k : ℤ) {m n : ℕ} (hmn : m.Coprime n) :
    idealCoefficient k (m * n) = idealCoefficient k m * idealCoefficient k n := by
  simp only [cube_coefficient, mul_pow]
  exact coefficient_mul (psiHom k) (hmn.pow 3 3)

theorem idealCoefficient_one (k : ℤ) : idealCoefficient k 1 = 1 := by
  rw [cube_coefficient, one_pow]
  exact coefficient_one (psiHom k)

end Cubic.BoxAsymptotic.IdealNormFibers
