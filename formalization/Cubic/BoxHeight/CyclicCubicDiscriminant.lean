import Cubic.BoxHeight.CyclicCubicFields

/-!
# `|Δ_{K_a}| ≤ c_a²`

Supporting lemma for `thm:lower` of `box_height_research_note.tex`, where `B_K = 8/c_K` uses
`Δ_K = c_K²`; only `|Δ_K| ≤ c_K²` (so `B_K ≥ 8/c_K`) is needed for the lower bound.

With `K = K_a ⊂ M = ℚ(ζ_c)`, `c = c_a` and `[M : K] = r = φ(c)/3`, the tower formula gives
`|Δ_K|^r ∣ |Δ_M| = c^{φ(c)} / ∏_{p ∣ c} p^{φ(c)/(p-1)}`. Compare `p`-adic valuations. If `p ∥ c`,
then `r v_p(Δ_K) ≤ 3r - φ(c)/(p-1) < 3r`, so `v_p(Δ_K) ≤ 2`. If `p = 3`, `9 ∥ c`, then
`r v_3(Δ_K) ≤ 6r - 3r/2`, so `v_3(Δ_K) ≤ 4`. Primes not dividing `c` do not divide `Δ_K`.
Hence `|Δ_K|` divides `c²`.
-/

noncomputable section

namespace Cubic.BoxHeight.CyclicCubicDiscriminant

open NumberField Polynomial Cubic.BoxHeight.CyclicCubicCharacters
open Cubic.BoxHeight.CyclicCubicFields

/-- The `p`-adic valuation of `∏_{x ∈ s} x^{k x}` for a set of primes `s`. -/
theorem factorization_prod_primes_pow {s : Finset ℕ} (hs : ∀ x ∈ s, x.Prime) (k : ℕ → ℕ)
    (p : ℕ) : (∏ x ∈ s, x ^ k x).factorization p = if p ∈ s then k p else 0 := by
  classical
  rw [Nat.factorization_prod fun x hx => pow_ne_zero _ (hs x hx).ne_zero, Finset.sum_apply']
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have h : ∀ x ∈ s, k x * x.factorization p = if x = p then k p else 0 := fun x hx => by
    rw [(hs x hx).factorization, Finsupp.single_apply]
    split_ifs with hxp
    · rw [hxp, mul_one]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']

/-- The valuation comparison. -/
theorem dvd_sq_of_pow_dvd {c r D : ℕ} (hc0 : c ≠ 0) (hD : D ≠ 0) (hr : 0 < r)
    (hφ : c.totient = 3 * r)
    (hc : ∀ p ∈ c.primeFactors, c.factorization p = 1 ∨ (p = 3 ∧ c.factorization p = 2))
    (hdvd : D ^ r ∣ c ^ c.totient / ∏ p ∈ c.primeFactors, p ^ (c.totient / (p - 1))) :
    D ∣ c ^ 2 := by
  set Pr := ∏ p ∈ c.primeFactors, p ^ (c.totient / (p - 1)) with hPrdef
  have hPr : Pr ∣ c ^ c.totient := Nat.prod_primeFactors_pow_totient_ediv_dvd (Nat.pos_of_ne_zero hc0)
  have hq0 : c ^ c.totient / Pr ≠ 0 := by
    have hPr0 : 0 < Pr := Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
    exact (Nat.div_pos (Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hc0) _) hPr) hPr0).ne'
  rw [← Nat.factorization_le_iff_dvd hD (pow_ne_zero 2 hc0)]
  intro p
  have h1 := (Nat.factorization_le_iff_dvd (pow_ne_zero r hD) hq0).mpr hdvd p
  rw [Nat.factorization_pow, Nat.factorization_div hPr, Nat.factorization_pow, hPrdef] at h1
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_tsub, Pi.sub_apply] at h1
  rw [factorization_prod_primes_pow (fun x hx => Nat.prime_of_mem_primeFactors hx)
    (fun x => c.totient / (x - 1))] at h1
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ c.primeFactors
  · rw [if_pos hp] at h1
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvdφ : p - 1 ∣ c.totient := by
      rw [← Nat.totient_prime hpp]
      exact Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨d, hd⟩ := hdvdφ
    have hp1 : 0 < p - 1 := by have := hpp.two_le; omega
    have hdiv : c.totient / (p - 1) = d := by
      rw [hd, Nat.mul_div_cancel_left _ hp1]
    rw [hdiv] at h1
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, mul_zero] at hd; omega
      · exact h0
    rcases hc p hp with h | ⟨rfl, h⟩
    · rw [h] at h1 ⊢
      by_contra hlt
      have : r * 3 ≤ r * D.factorization p := Nat.mul_le_mul_left r (by omega)
      omega
    · rw [h] at h1 ⊢
      have hd2 : 2 * d = 3 * r := by rw [← hφ, hd]
      by_contra hlt
      have : r * 5 ≤ r * D.factorization 3 := Nat.mul_le_mul_left r (by omega)
      omega
  · rw [if_neg hp] at h1
    have hc0p : c.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    rw [hc0p, mul_zero, Nat.sub_zero] at h1
    rw [hc0p]
    have : D.factorization p * r = 0 := by rw [mul_comm]; omega
    rcases Nat.mul_eq_zero.mp this with h | h
    · omega
    · omega

variable {P : SplitSet}

/-- The prime of a modulus: `9 = 3²`, `p = p¹`. -/
def qprime : ι P → ℕ
  | none => 3
  | some p => p.1

def qexp : ι P → ℕ
  | none => 2
  | some _ => 1

theorem q_eq (i : ι P) : q P i = qprime i ^ qexp i := by
  cases i <;> simp [q, qprime, qexp]

theorem qprime_prime (i : ι P) : (qprime i).Prime := by
  cases i with
  | none => exact Nat.prime_three
  | some p => exact P.prime p.1 p.2

theorem qprime_injective : Function.Injective (qprime (P := P)) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some p' =>
      have := P.mod_three p'.1 p'.2
      simp only [qprime] at h; omega
  | some p =>
    cases j with
    | none =>
      have := P.mod_three p.1 p.2
      simp only [qprime] at h; omega
    | some p' =>
      simp only [qprime] at h
      exact congrArg some (Subtype.ext h)

theorem factorization_cond (a : ι P → ZMod 3) (p : ℕ) (hp : p ∈ (CyclicCubicCharacters.cond P a).primeFactors) :
    (CyclicCubicCharacters.cond P a).factorization p = 1 ∨ (p = 3 ∧ (CyclicCubicCharacters.cond P a).factorization p = 2) := by
  classical
  have hfac : (CyclicCubicCharacters.cond P a).factorization p = ∑ i ∈ supp P a, (q P i).factorization p := by
    rw [CyclicCubicCharacters.cond, Nat.factorization_prod fun i _ => (q_pos P i).ne', Finset.sum_apply']
  have hterm : ∀ i, (q P i).factorization p = if qprime i = p then qexp i else 0 := by
    intro i
    rw [q_eq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      (qprime_prime i).factorization, Finsupp.single_apply]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  simp only [hterm] at hfac
  have hpos : 0 < (CyclicCubicCharacters.cond P a).factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (cond_pos P a).ne'
      (Nat.dvd_of_mem_primeFactors hp)
  -- some index has prime `p`
  obtain ⟨i, hi, hip⟩ : ∃ i ∈ supp P a, qprime i = p := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero fun i hi => if_neg (hne i hi)] at hfac
    omega
  rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (qprime_injective (h.trans hip.symm)))
    (fun h => absurd hi h), if_pos hip] at hfac
  cases i with
  | none => exact Or.inr ⟨hip.symm, by rw [hfac]; rfl⟩
  | some p' => exact Or.inl (by rw [hfac]; rfl)

set_option synthInstance.maxHeartbeats 200000

/-- `K_a` as a subfield of `M_a`. -/
abbrev Kr (a : ι P → ZMod 3) : IntermediateField ℚ (M P a) :=
  IntermediateField.restrict (K_le_M a)

theorem natAbs_discr_Kr_pow_dvd (a : ι P → ZMod 3) :
    (discr (Kr a)).natAbs ^ Module.finrank (Kr a) (M P a) ∣ (discr (M P a)).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (Kr a) (𝓞 (Kr a)) (M P a)
    (𝓞 (M P a))]
  exact dvd_mul_left _ _

theorem discr_Kr (a : ι P → ZMod 3) : discr (Kr a) = discr (K P a) :=
  (discr_eq_discr_of_algEquiv _ (IntermediateField.restrict_algEquiv (K_le_M a))).symm

/-- `|Δ_{K_a}|` divides `c_a²`. -/
theorem natAbs_discr_dvd {a : ι P → ZMod 3} (ha : a ≠ 0) :
    (discr (K P a)).natAbs ∣ CyclicCubicCharacters.cond P a ^ 2 := by
  set r := Module.finrank (Kr a) (M P a)
  have hM : Module.finrank ℚ (M P a) = (CyclicCubicCharacters.cond P a).totient :=
    IsCyclotomicExtension.finrank (M P a) (cyclotomic.irreducible_rat (cond_pos P a))
  have hK : Module.finrank ℚ (Kr a) = 3 := by
    rw [← (IntermediateField.restrict_algEquiv (K_le_M a)).toLinearEquiv.finrank_eq, finrank_K ha]
  have hφ : (CyclicCubicCharacters.cond P a).totient = 3 * r := by
    rw [← hM, ← hK]; exact (Module.finrank_mul_finrank ℚ (Kr a) (M P a)).symm
  have hr : 0 < r := Module.finrank_pos (R := Kr a) (M := M P a)
  have hdvd := natAbs_discr_Kr_pow_dvd a
  rw [IsCyclotomicExtension.Rat.natAbs_discr (CyclicCubicCharacters.cond P a) (M P a), discr_Kr] at hdvd
  exact dvd_sq_of_pow_dvd (cond_pos P a).ne' (by simpa using discr_ne_zero (K P a)) hr hφ
    (factorization_cond a) hdvd

theorem abs_discr_le {a : ι P → ZMod 3} (ha : a ≠ 0) :
    |(discr (K P a) : ℝ)| ≤ (CyclicCubicCharacters.cond P a : ℝ) ^ 2 := by
  have h := Nat.le_of_dvd (pow_pos (cond_pos P a) 2) (natAbs_discr_dvd ha)
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast h

end Cubic.BoxHeight.CyclicCubicDiscriminant
