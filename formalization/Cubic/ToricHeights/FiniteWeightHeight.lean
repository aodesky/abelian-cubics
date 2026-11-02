import Cubic.ToricHeights.LocalWeightHeight
import Cubic.ToricHeights.QuotientInvariantIntegrality
import Cubic.PoissonSummation.FiniteAdelicData
import Cubic.PoissonSummation.QuotientFiniteFourierProduct
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Finite local heights at integral points, from the weight vectors

In the proof of `prop:canonicalHeight`, a `D₀`-integral point contributes only
at the complex place. By `eqn:localHeight` a finite factor is one exactly when
the three weight-vector values are `w`-integral. The value `1-3e₂` is integral
at once. The two conjugate values `z±` have sum `2-9e₂+27e₃` and product
`(1-3e₂)³` (the paper's short computation), so they are roots of a monic
quadratic with integral coefficients, hence integral by the ultrametric
inequality. The paper states this step without argument.
-/

noncomputable section

namespace Cubic.ToricHeights.FiniteWeightHeight

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois QuotientLocalCharacters DescendedCoefficients
open WeightVectors LocalWeightHeight

/-- A root of a monic quadratic with coefficients of norm at most one has norm at most one. -/
theorem quadratic_norm_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] {x S T : L}
    (h : x ^ 2 - S * x + T = 0) (hS : ‖S‖ ≤ 1) (hT : ‖T‖ ≤ 1) : ‖x‖ ≤ 1 := by
  by_contra hx
  push_neg at hx
  have hx2 : x ^ 2 = S * x + -T := by linear_combination h
  have hmax := IsUltrametricDist.norm_add_le_max (S * x) (-T)
  rw [← hx2, norm_pow, norm_mul, norm_neg] at hmax
  have h₁ : ‖S‖ * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg S]
  have h₂ : max (‖S‖ * ‖x‖) ‖T‖ ≤ ‖x‖ := max_le h₁ (by linarith)
  nlinarith

section Values

variable (A : Type*) [CommRing A] [Algebra ℚ A]
variable {L : Type*} [NormedField L] [CharZero L] [IsUltrametricDist L]
variable (place : E ⊗[ℚ] A →+* L)

/-- All three nontrivial weight-vector values are integral when `e₂` and `e₃` are. -/
theorem character_norm_le_one (P : quotientFixedRing →ₐ[ℚ] A)
    (ha : ‖place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient)‖ ≤ 1)
    (hc : ‖place ((1 : E) ⊗ₜ[ℚ] P constantCoefficient)‖ ≤ 1)
    (m : ℤ × ℤ) (hm : m = (1, 1) ∨ m = (2, 1) ∨ m = (1, 2)) :
    ‖((localCharacter A place P (Multiplicative.ofAdd m) : Lˣ) : L)‖ ≤ 1 := by
  set a := place ((1 : E) ⊗ₜ[ℚ] P linearCoefficient)
  set c := place ((1 : E) ⊗ₜ[ℚ] P constantCoefficient)
  have hn : ∀ n : ℕ, ‖(n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L
  have hsub : ∀ x y : L, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hint : ∀ (k l : ℕ), ‖(k : L) * a‖ ≤ 1 ∧ ‖(l : L) * c‖ ≤ 1 := fun k l =>
    ⟨by rw [norm_mul]; nlinarith [hn k, norm_nonneg a, norm_nonneg (k : L)],
      by rw [norm_mul]; nlinarith [hn l, norm_nonneg c, norm_nonneg (l : L)]⟩
  have hN : ‖1 - 3 * a‖ ≤ 1 := by
    have := hsub (1 : L) (3 * a)
    have h3 := (hint 3 0).1
    push_cast at h3
    exact this.trans (max_le (by simp) h3)
  have hS : ‖2 - 9 * a - 27 * c‖ ≤ 1 := by
    have h1 := hsub (2 - 9 * a) (27 * c)
    have h2 := hsub (2 : L) (9 * a)
    have h9 := (hint 9 27).1
    have h27 := (hint 9 27).2
    push_cast at h9 h27
    have h2' : ‖(2 : L)‖ ≤ 1 := by exact_mod_cast hn 2
    exact h1.trans (max_le (h2.trans (max_le h2' h9)) h27)
  have hT : ‖(1 - 3 * a) ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hN
  obtain ⟨h₂₁, h₁₂⟩ := character_eq_weightValue A place P
  have hsum : weightValue A place 1 P + weightValue A place (-1) P = 2 - 9 * a - 27 * c := by
    rw [weightValue, weightValue, place_tmul]
    push_cast
    ring
  have hprod := weightValue_mul A place P
  rcases hm with rfl | rfl | rfl
  · rw [normCharacter_value]
    exact hN
  · rw [h₂₁]
    exact quadratic_norm_le_one (S := 2 - 9 * a - 27 * c) (T := (1 - 3 * a) ^ 3)
      (by rw [← hsum, ← hprod]; ring) hS hT
  · rw [h₁₂]
    exact quadratic_norm_le_one (S := 2 - 9 * a - 27 * c) (T := (1 - 3 * a) ^ 3)
      (by rw [← hsum, ← hprod]; ring) hS hT

end Values

/-- A maximum of local absolute values with nonnegative orders is one. -/
theorem max_weights_one {q : ℝ} (hq : 1 < q) {o₁ o₂ o₃ : ℝ} (h₁ : 0 ≤ o₁) (h₂ : 0 ≤ o₂)
    (h₃ : 0 ≤ o₃) :
    (max (max 1 (localAbs q o₁)) (max (localAbs q o₂) (localAbs q o₃))) ^ (1 / 2 : ℝ) = 1 := by
  have hle : ∀ o : ℝ, 0 ≤ o → localAbs q o ≤ 1 := fun o ho =>
    Real.rpow_le_one_of_one_le_of_nonpos hq.le (by linarith)
  rw [max_eq_left (max_le (hle _ h₂) (hle _ h₃) |>.trans (le_max_left _ _)),
    max_eq_left (hle _ h₁), Real.one_rpow]

/-- A finite local factor of the height of `O(3D₀)` is one when all weight orders are nonnegative. -/
theorem finite_factor_one (A : Type*) [CommRing A] [Algebra ℚ A] {L : Type*} [Field L]
    (place : E ⊗[ℚ] A →+* L) (ord : Lˣ →* Multiplicative ℤ) (q : ℕ) (hq : 1 < q)
    (P : quotientFixedRing →ₐ[ℚ] A)
    (hord : ∀ m : ℤ × ℤ, (m = (1, 1) ∨ m = (2, 1) ∨ m = (1, 2)) →
      0 ≤ (ord (localCharacter A place P (Multiplicative.ofAdd m))).toAdd) :
    (q : ℂ) ^ (supportFunction (-3) 0
        (QuotientFiniteHeight.realCoordinates (localCocharacter A place ord P)) /
          Module.finrank ℚ E) = 1 := by
  rw [finite_localHeight A place ord q hq P, characterAbs, characterAbs, characterAbs,
    max_weights_one (by exact_mod_cast hq)
      (by exact_mod_cast hord _ (Or.inl rfl)) (by exact_mod_cast hord _ (Or.inr (Or.inl rfl)))
      (by exact_mod_cast hord _ (Or.inr (Or.inr rfl)))]
  simp

open QuotientFiniteHeight Cubic.PoissonSummation QuotientFiniteFourierProduct

private theorem split_scalar (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (a : ℚ_[p]) :
    SplitQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a) = a ∧
      SplitQuotientLogarithm.secondPlace p ((1 : E) ⊗ₜ[ℚ] a) = a := by
  simp [SplitQuotientLogarithm.place, SplitQuotientLogarithm.secondPlace,
    SplitQuotientLogarithm.splitting_scalar]

/-- At a split prime both places give local factor one on the integral locus. -/
theorem split_height_one (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hx : x ∈ QuotientInvariantIntegrality.invariantLocus p) :
    splitInverseHeight p (-3) 0 x = 1 := by
  obtain ⟨ha, hc, -⟩ := hx
  rw [norm_neg] at hc
  have hq : 1 < Nat.card (IsLocalRing.ResidueField ℤ_[p]) := by
    rw [LocalLogarithmNormalization.padic_residue_cardinality]
    exact (Fact.out : p.Prime).one_lt
  have hplace : ∀ place : E ⊗[ℚ] ℚ_[p] →+* ℚ_[p], (∀ a, place ((1 : E) ⊗ₜ[ℚ] a) = a) →
      (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^ (supportFunction (-3) 0
        (realCoordinates (localCocharacter ℚ_[p] place
          (Cubic.OrbitParametrization.PadicMultiplicative.valuation p) x)) /
          Module.finrank ℚ E) = 1 := by
    intro place hs
    apply finite_factor_one _ place _ _ hq
    intro m hm
    change 0 ≤ Padic.valuation _
    rw [← Padic.norm_le_one_iff_val_nonneg]
    exact character_norm_le_one ℚ_[p] place x (by rw [hs]; exact ha) (by rw [hs]; exact hc) m hm
  rw [splitInverseHeight, splitCoordinates, splitSecondCoordinates,
    hplace _ (fun a => (split_scalar p a).1), hplace _ (fun a => (split_scalar p a).2), one_mul]

/-- At an inert prime the single local factor is one on the integral locus. -/
theorem inert_height_one (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) (hx : x ∈ QuotientInvariantIntegrality.invariantLocus p) :
    inertInverseHeight p (-3) 0 x = 1 := by
  obtain ⟨ha, hc, -⟩ := hx
  rw [norm_neg] at hc
  have hq : 1 < Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)) := by
    rw [CyclotomicInertField.card_residueField]
    exact Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
  have hs : ∀ a : ℚ_[p], ‖(InertQuotientLogarithm.place p).toRingHom ((1 : E) ⊗ₜ[ℚ] a)‖ = ‖a‖ :=
    fun a => by
      change ‖InertQuotientLogarithm.place p ((1 : E) ⊗ₜ[ℚ] a)‖ = _
      rw [InertQuotientLogarithm.place_scalar, CyclotomicInertField.norm_algebraMap]
  rw [inertInverseHeight, inertCoordinates]
  apply finite_factor_one _ _ _ _ hq
  intro m hm
  change 0 ≤ InertLocalModel.ord p _
  rw [← InertLocalModel.norm_le_one_iff_ord_nonneg]
  exact character_norm_le_one ℚ_[p] _ x (by rw [hs]; exact ha) (by rw [hs]; exact hc) m hm

/-- At the ramified prime the single local factor is one on the integral locus. -/
theorem ramified_height_one (x : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hx : x ∈ QuotientInvariantIntegrality.invariantLocus 3) :
    ramifiedInverseHeight (-3) 0 x = 1 := by
  obtain ⟨ha, hc, -⟩ := hx
  rw [norm_neg] at hc
  have hq : 1 < Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers) := by
    rw [CyclotomicRamifiedField.card_residueField]
    norm_num
  have hs : ∀ a : ℚ_[3], ‖RamifiedQuotientLogarithm.place.toRingHom ((1 : E) ⊗ₜ[ℚ] a)‖ = ‖a‖ :=
    fun a => by
      change ‖RamifiedQuotientLogarithm.place ((1 : E) ⊗ₜ[ℚ] a)‖ = _
      rw [RamifiedQuotientLogarithm.place_scalar, CyclotomicRamifiedField.norm_algebraMap]
  rw [ramifiedInverseHeight, ramifiedCoordinates]
  apply finite_factor_one _ _ _ _ hq
  intro m hm
  change 0 ≤ RamifiedLocalModel.ord _
  have hn := character_norm_le_one ℚ_[3] _ x (by rw [hs]; exact ha) (by rw [hs]; exact hc) m hm
  have hsq := RamifiedLocalModel.norm_sq_eq_zpow_ord
    (localCharacter ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom x (Multiplicative.ofAdd m))
  by_contra hneg
  push_neg at hneg
  have h1 : (1 : ℝ) < 3 ^ (-RamifiedLocalModel.ord
      (localCharacter ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom x
        (Multiplicative.ofAdd m))) :=
    one_lt_zpow₀ (by norm_num) (by linarith)
  have h2 : ‖((localCharacter ℚ_[3] RamifiedQuotientLogarithm.place.toRingHom x
      (Multiplicative.ofAdd m) : CyclotomicRamifiedField.Extensionˣ) :
        CyclotomicRamifiedField.Extension)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  linarith

/-- Every finite local factor of the height of `O(3D₀)` is one at a `D₀`-integral local point. -/
theorem local_height_one (p : Nat.Primes) :
    ∀ x ∈ (family p).integralLocus, (family p).inverseHeight (-3) 0 x = 1 := by
  apply FiniteAdelicData.localLogarithm_induction
    (fun D _ => ∀ x ∈ D.integralLocus, D.inverseHeight (-3) 0 x = 1)
  · intro p x hx
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
    exact split_height_one p.1 x hx
  · intro p x hx
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩
    exact inert_height_one p.1 x hx
  · intro x hx
    exact ramified_height_one x hx

end Cubic.ToricHeights.FiniteWeightHeight
