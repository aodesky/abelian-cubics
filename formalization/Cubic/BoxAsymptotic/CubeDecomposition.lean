import Cubic.PoissonSummation.CyclotomicIntegerUnits
import Cubic.Counting.EisensteinNormCount
import Cubic.QuadraticCorrespondence.CyclotomicNormTrace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Elements of `ℤ[ζ]` whose norm is a cube

Supporting step for `lem:sector`: if `N β = n³`, then `β = u · N(γ) · γ · δ³` with `u` a unit
and `γ` primitive (divisible by no rational integer other than `±1`).

Proof via prime ideals, with `τ` complex conjugation. Write `e(P)` for the exponent of `P` in
`(β)`. Since `β τ(β) = n³`, `e(P) + e(τP) = 3 f(P)` with `f` the exponents of `(n)`; in
particular `e(P) ≡ 0 (mod 3)` when `τP = P`. Put `Γ = Π_{e(P) ≡ 2} P`. Then
`(β) = Γ² τ(Γ) D³` for an integral ideal `D`, and a generator `γ` of `Γ` satisfies
`Γ τ(Γ) = (N γ)`. A rational prime dividing `γ` would give `P, τP` both dividing `Γ`, which
the exponents rule out.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.CubeDecomposition

open NumberField UniqueFactorizationMonoid
open Cubic.QuadraticCorrespondence.CyclotomicField Cubic.PoissonSummation.CyclotomicIntegerUnits

/-- Complex conjugation on `𝒪 = ℤ[ζ]`. -/
def τ : Integers ≃+* Integers := RingOfIntegers.mapRingEquiv conjugation.toRingEquiv

theorem coe_τ (x : Integers) : ((τ x : Integers) : E) = conjugation (x : E) := rfl

theorem τ_τ (x : Integers) : τ (τ x) = x := by
  apply RingOfIntegers.coe_injective
  exact conjugation_involutive (x : E)

theorem mul_τ (x : Integers) : x * τ x = ((Algebra.norm ℤ x : ℤ) : Integers) := by
  apply RingOfIntegers.coe_injective
  have h := norm_eq_mul_conjugation (x : E)
  have h2 := Algebra.coe_norm_int (K := E) x
  push_cast
  rw [← h2] at h
  change (x : E) * conjugation (x : E) = _
  rw [← h]
  simp

/-- `τ` on ideals. -/
def τI : Ideal Integers →*₀ Ideal Integers := Ideal.mapHom τ.toRingHom

theorem τI_apply (I : Ideal Integers) : τI I = I.map τ := rfl

theorem τI_τI (I : Ideal Integers) : τI (τI I) = I := by
  have hs : τ.symm = τ := RingEquiv.ext fun x => by
    rw [RingEquiv.symm_apply_eq, τ_τ]
  rw [τI_apply, τI_apply]
  conv_lhs => rw [← hs]
  exact Ideal.map_of_equiv τ

theorem τI_span (x : Integers) : τI (Ideal.span {x}) = Ideal.span {τ x} := by
  rw [τI_apply, Ideal.map_span, Set.image_singleton]

theorem τI_injective : Function.Injective τI :=
  Function.LeftInverse.injective τI_τI

theorem τI_ne_zero {I : Ideal Integers} (h : I ≠ 0) : τI I ≠ 0 := by
  rw [Ne, ← map_zero τI]; exact fun he => h (τI_injective he)

theorem τI_prime {P : Ideal Integers} (hP : Prime P) : Prime (τI P) := by
  have hne : P ≠ ⊥ := hP.ne_zero
  have hip : P.IsPrime := (Ideal.prime_iff_isPrime hne).mp hP
  rw [Ideal.prime_iff_isPrime (τI_ne_zero hne)]
  exact Ideal.map_isPrime_of_equiv τ

theorem normalizedFactors_τI {I : Ideal Integers} (hI : I ≠ 0) :
    normalizedFactors (τI I) = (normalizedFactors I).map τI := by
  have hprime : ∀ P ∈ (normalizedFactors I).map τI, Prime P := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hP
    exact τI_prime (prime_of_normalized_factor Q hQ)
  rw [← normalizedFactors_prod_of_prime hprime, ← map_multiset_prod,
    associated_iff_eq.mp (prod_normalizedFactors hI)]


theorem τ_intCast (k : ℤ) : τ (k : Integers) = k := map_intCast τ k

/-- A rational integer that is a unit of `𝒪` is `±1`. -/
theorem isUnit_of_isUnit_cast {k : ℤ} (h : IsUnit (k : Integers)) : IsUnit k := by
  have h1 := h.map (Algebra.norm ℤ)
  rw [show (k : Integers) = algebraMap ℤ Integers k from (eq_intCast _ k).symm,
    Algebra.norm_algebraMap_of_basis integralPowerBasis.basis, Fintype.card_fin] at h1
  exact (isUnit_pow_iff integralPowerBasis.dim_ne_zero).mp h1

open scoped Classical in
/-- **Cube decomposition.** If `β τ(β) = n³` with `n ≠ 0`, then `β = u · N(γ) · γ · δ³` with
`u` a unit and `γ` divisible by no rational integer other than `±1`. -/
theorem decomposition {β : Integers} {n : ℤ} (hβ : β * τ β = (n : Integers) ^ 3) (hn : n ≠ 0) :
    ∃ (u : Integersˣ) (γ δ : Integers), γ ≠ 0 ∧
      β = u * (γ * τ γ) * γ * δ ^ 3 ∧ ∀ k : ℤ, (k : Integers) ∣ γ → IsUnit k := by
  have hn' : (n : Integers) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_mul] at hβ; exact pow_ne_zero 3 hn' hβ.symm
  set I : Ideal Integers := Ideal.span {β} with hIdef
  set M : Ideal Integers := Ideal.span {(n : Integers)}
  have hI : I ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ0
  have hM : M ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn'
  have hIM : I * τI I = M ^ 3 := by
    rw [hIdef, τI_span, Ideal.span_singleton_mul_span_singleton, hβ, Ideal.span_singleton_pow]
  set s := normalizedFactors I with hs
  -- the exponents of `P` and `τP` add up to a multiple of `3`
  have key : ∀ P, s.count P + s.count (τI P) = 3 * (normalizedFactors M).count P := by
    intro P
    have h := congrArg (Multiset.count P) (congrArg normalizedFactors hIM)
    rw [normalizedFactors_mul hI (τI_ne_zero hI), normalizedFactors_pow, normalizedFactors_τI hI,
      Multiset.count_add, Multiset.count_nsmul] at h
    rw [← h, ← τI_τI P, Multiset.count_map_eq_count' _ _ τI_injective, τI_τI]
  -- `Γ`: the primes with exponent `≡ 2 (mod 3)`, and `D`: the cube root of the rest
  set g : Multiset (Ideal Integers) := (s.toFinset.filter (fun P => s.count P % 3 = 2)).val
  have hg : ∀ P, g.count P = if s.count P % 3 = 2 then 1 else 0 := by
    intro P
    rw [Multiset.count_eq_of_nodup (Finset.nodup _)]
    by_cases h : s.count P % 3 = 2
    · rw [if_pos h, if_pos]
      simp only [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨Multiset.count_pos.mp (by omega), h⟩
    · rw [if_neg h, if_neg]
      simp only [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset]
      exact fun h' => h h'.2
  set d : Ideal Integers → ℕ := fun P =>
    (s.count P - 2 * g.count P - g.count (τI P)) / 3
  set D : Multiset (Ideal Integers) := s.toFinset.val.bind (fun P => Multiset.replicate (d P) P)
  have hD : ∀ P, D.count P = if P ∈ s then d P else 0 := by
    intro P
    rw [Multiset.count_bind, ← Finset.sum_eq_multiset_sum]
    simp_rw [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    simp only [Multiset.mem_toFinset]
  have hsplit : s = 2 • g + g.map τI + 3 • D := by
    ext P
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
      ← τI_τI P, Multiset.count_map_eq_count' _ _ τI_injective, τI_τI, hD]
    have k1 := key P
    have k2 := hg P
    have k3 := hg (τI P)
    simp only [d]
    by_cases hP : P ∈ s
    · rw [if_pos hP]
      split_ifs at k2 k3 <;> omega
    · rw [if_neg hP]
      have h0 := Multiset.count_eq_zero.mpr hP
      split_ifs at k2 k3 <;> omega
  -- generators
  set Γ := g.prod
  set Δ := D.prod
  have hIeq : I = Γ ^ 2 * τI Γ * Δ ^ 3 := by
    rw [← associated_iff_eq.mp (prod_normalizedFactors hI), ← hs]
    conv_lhs => rw [hsplit]
    rw [Multiset.prod_add, Multiset.prod_add, Multiset.prod_nsmul, Multiset.prod_nsmul,
      ← map_multiset_prod]
  set γ := Cubic.Counting.EisensteinNormCount.gen Γ
  set δ := Cubic.Counting.EisensteinNormCount.gen Δ
  have hΓ : Ideal.span {γ} = Γ := Cubic.Counting.EisensteinNormCount.span_gen Γ
  have hΔ : Ideal.span {δ} = Δ := Cubic.Counting.EisensteinNormCount.span_gen Δ
  have hspan : Ideal.span {β} = Ideal.span {γ ^ 2 * τ γ * δ ^ 3} := by
    rw [← hIdef, hIeq, ← hΓ, ← hΔ, τI_span, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  have hγ0 : γ ≠ 0 := by
    rintro h0
    rw [h0] at hu
    simp at hu
    exact hβ0 hu.symm
  refine ⟨u, γ, δ, hγ0, by rw [← hu]; ring, fun k hk => ?_⟩
  -- primitivity
  by_contra hku
  have hk0 : (k : Integers) ≠ 0 := by
    rintro h0; rw [h0, zero_dvd_iff] at hk; exact hγ0 hk
  have htop : Ideal.span {(k : Integers)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => hku (isUnit_of_isUnit_cast h)
  obtain ⟨P, hPmax, hPk⟩ := Ideal.exists_le_maximal _ htop
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hk0 (Ideal.span_singleton_eq_bot.mp (le_bot_iff.mp hPk))
  have hPprime : Prime P := (Ideal.prime_iff_isPrime hPbot).mpr hPmax.isPrime
  have hγk : Ideal.span {γ} ≤ Ideal.span {(k : Integers)} :=
    Ideal.span_singleton_le_span_singleton.mpr hk
  have hmem : ∀ Q : Ideal Integers, Prime Q → Q ∣ Γ → Q ∈ g := by
    intro Q hQ hQΓ
    obtain ⟨R, hR, hQR⟩ := hQ.exists_mem_multiset_dvd hQΓ
    have hRp : Prime R := by
      obtain ⟨R', hR', rfl⟩ := Multiset.mem_map.mp (Multiset.map_id' g ▸ hR)
      have : R' ∈ s := by
        have := Multiset.mem_of_mem_nsmul (n := 1) (by simpa using hR')
        simp only [g, Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset] at this
        exact this.1
      exact prime_of_normalized_factor R' this
    rw [associated_iff_eq.mp ((hQ.dvd_prime_iff_associated hRp).mp hQR)]
    exact hR
  have h1 : P ∈ g := hmem P hPprime (Ideal.dvd_iff_le.mpr (hΓ ▸ hγk.trans hPk))
  have h2 : τI P ∈ g := by
    refine hmem _ (τI_prime hPprime) (Ideal.dvd_iff_le.mpr ?_)
    rw [← hΓ]
    refine hγk.trans ?_
    have := Ideal.map_mono (f := τ) hPk
    rw [Ideal.map_span, Set.image_singleton] at this
    exact (le_of_eq (by rw [τ_intCast])).trans this
  have c1 := hg P
  have c2 := hg (τI P)
  rw [if_pos (by
    simp only [g, Finset.mem_val, Finset.mem_filter] at h1; exact h1.2)] at c1
  rw [if_pos (by
    simp only [g, Finset.mem_val, Finset.mem_filter] at h2; exact h2.2)] at c2
  have k1 := key P
  simp only [g, Finset.mem_val, Finset.mem_filter] at h1 h2
  omega

end Cubic.BoxAsymptotic.CubeDecomposition
