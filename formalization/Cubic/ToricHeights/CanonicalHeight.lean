import Cubic.ToricHeights.FiniteWeightHeight
import Cubic.PoissonSummation.IntegralPointComparison
import Cubic.PoissonSummation.AdelicHeightLaws
import Cubic.QuadraticCorrespondence.CorrespondencePolynomialArithmetic
import CubicTargets.ToricHeights.CanonicalHeight

/-!
# `prop:canonicalHeight`

The proof follows the paper.

1. The coefficients of the descended cubic are `e₂` and `-e₃`, so
   `lemma:affineIntegrality` (`IntegralPointComparison.coefficient_criterion`)
   gives the integrality assertion.
2. The support function of `3D₀` is expressed through the weight vectors
   (`LocalWeightHeight`, `eqn:localHeight`).
3. At a `D₀`-integral point every finite factor is one (`FiniteWeightHeight`).
4. At the complex place the three values are `|1-3e₂|²`, `|z₊|²` and `|z₋|²`, and
   the short computation gives `|z±|² = z₊z₋ = (1-3e₂)³`
   (`eqn:heightExtraFactor`). Since `(1-3e₂)³ ≥ 0` and `1-3e₂` is an integer
   congruent to one modulo three, `1-3e₂ ≥ 1`, so the maximum is `(1-3e₂)³`.
5. `H(P,O(D₀)) = H(P,O(3D₀))^{1/3} = √(1-3e₂)`.
-/

noncomputable section

namespace Cubic.ToricHeights.CanonicalHeight

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois QuotientLocalCharacters DescendedCoefficients CorrespondencePolynomials
open WeightVectors LocalWeightHeight FiniteWeightHeight QuotientFiniteHeight
open Cubic.PoissonSummation QuotientFiniteFourierProduct AdelicHeightZetaData RationalAdelicEmbedding

/-! ### `H(-,O(3D₀)) = H(-,O(D₀))³` at every place -/

private theorem cpow_three (q s D : ℂ) (n : ℝ × ℝ) :
    q ^ (supportFunction (3 * s) 0 n / D) = (q ^ (supportFunction s 0 n / D)) ^ 3 := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  simp only [supportFunction, Nat.cast_ofNat]
  ring

theorem local_cube (p : Nat.Primes) (s : ℂ) :
    ∀ x, (family p).inverseHeight (3 * s) 0 x = ((family p).inverseHeight s 0 x) ^ 3 := by
  apply FiniteAdelicData.localLogarithm_induction
    (fun D _ => ∀ x, D.inverseHeight (3 * s) 0 x = (D.inverseHeight s 0 x) ^ 3)
  · intro p x
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
    change splitInverseHeight p.1 (3 * s) 0 x = (splitInverseHeight p.1 s 0 x) ^ 3
    rw [splitInverseHeight, splitInverseHeight, cpow_three, cpow_three, mul_pow]
  · intro p x
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩
    change inertInverseHeight p.1 (3 * s) 0 x = (inertInverseHeight p.1 s 0 x) ^ 3
    rw [inertInverseHeight, inertInverseHeight, cpow_three]
  · intro x
    change ramifiedInverseHeight (3 * s) 0 x = (ramifiedInverseHeight s 0 x) ^ 3
    rw [ramifiedInverseHeight, ramifiedInverseHeight, cpow_three]

theorem finite_cube (s : ℂ) (x : FiniteAdelicData.Points) :
    FiniteAdelicData.inverseHeight (3 * s) 0 x = (FiniteAdelicData.inverseHeight s 0 x) ^ 3 := by
  classical
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.property
  have hS : ∀ p ∉ hfin.toFinset, x p ∈ (family p).maxCompact := by
    intro p hp
    by_contra hn
    exact hp (hfin.mem_toFinset.mpr hn)
  rw [FiniteAdelicData.inverseHeight_eq_prod (3 * s) 0 x _ hS,
    FiniteAdelicData.inverseHeight_eq_prod s 0 x _ hS, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun p _ => local_cube p s (x p)

theorem height_cube (s : ℂ) (x : AdelicData.Points) :
    height (3 * s) 0 x = (height s 0 x) ^ 3 := by
  simp only [height, AdelicData.inverseHeight, neg_zero, mul_pow]
  rw [show -(3 * s) = 3 * -s by ring, finite_cube, ArchimedeanQuotientLogarithm.inverseHeight,
    ArchimedeanQuotientLogarithm.inverseHeight, cpow_three]

/-- At a rational point the height of `O(D₀)` is a nonnegative real number. -/
theorem height_eq_norm (x : AdelicData.Points) :
    height 1 0 x = ((‖height 1 0 x‖ : ℝ) : ℂ) := by
  have h := AdelicHeightLaws.norm_inverseHeight (-1) 0 x
  simp only [Complex.neg_re, Complex.one_re, Complex.zero_re] at h
  push_cast at h
  simp only [height, neg_zero]
  exact h.symm

/-! ### The complex place -/

section Archimedean

variable (P : quotientFixedRing →ₐ[ℚ] ℚ)

private abbrev realPoint : ArchimedeanQuotientLogarithm.Points := baseChange ℝ P

private abbrev complexPlace : E ⊗[ℚ] ℝ →+* ℂ := CyclotomicArchimedean.place.toRingHom

private theorem place_rational (f : quotientFixedRing) :
    complexPlace ((1 : E) ⊗ₜ[ℚ] realPoint P f) = ((P f : ℝ) : ℂ) := by
  change CyclotomicArchimedean.place ((1 : E) ⊗ₜ[ℚ] (baseChange ℝ P f)) = _
  rw [baseChange_apply, CyclotomicArchimedean.place_scalar]
  rfl

private theorem conj_character :
    star ((localCharacter ℝ complexPlace (realPoint P) (Multiplicative.ofAdd (2, 1)) : ℂˣ) : ℂ) =
      ((localCharacter ℝ complexPlace (realPoint P) (Multiplicative.ofAdd (1, 2)) : ℂˣ) : ℂ) := by
  rw [ArchimedeanQuotientLogarithm.characterValue_eq, ArchimedeanQuotientLogarithm.characterValue_eq]
  have hc : ∀ w : ℂ, Complex.conjAe.toMulEquiv.toMonoidHom w = star w := fun _ => rfl
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_map, hc]
  simp only [zpow_ofNat, star_mul, star_pow, star_star]

/-- The paper's `|z₊|² = |z₋|² = (1-3e₂)³` at the complex place. -/
theorem archimedeanAbs_cubic (m : ℤ × ℤ) (hm : m = (2, 1) ∨ m = (1, 2)) :
    archimedeanAbs (realPoint P) m = (1 - 3 * (P linearCoefficient : ℝ)) ^ 3 := by
  obtain ⟨h₂₁, h₁₂⟩ := character_eq_weightValue ℝ complexPlace (realPoint P)
  have hprod := weightValue_mul ℝ complexPlace (realPoint P)
  rw [← h₂₁, ← h₁₂, place_rational] at hprod
  set z := ((localCharacter ℝ complexPlace (realPoint P) (Multiplicative.ofAdd (2, 1)) : ℂˣ) : ℂ)
  have hz : ((‖z‖ ^ 2 : ℝ) : ℂ) = (((1 - 3 * (P linearCoefficient : ℝ)) ^ 3 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    change z * star z = _
    rw [conj_character, hprod]
    push_cast
    ring
  have hz' : ‖z‖ ^ 2 = (1 - 3 * (P linearCoefficient : ℝ)) ^ 3 := by exact_mod_cast hz
  rcases hm with rfl | rfl
  · rw [archimedeanAbs_eq]
    exact hz'
  · rw [archimedeanAbs_eq, ← conj_character, norm_star]
    exact hz'

theorem archimedeanAbs_norm :
    archimedeanAbs (realPoint P) (1, 1) = (1 - 3 * (P linearCoefficient : ℝ)) ^ 2 := by
  rw [archimedeanAbs_eq, normCharacter_value, place_rational]
  rw [show (1 : ℂ) - 3 * ((P linearCoefficient : ℝ) : ℂ) =
      ((1 - 3 * (P linearCoefficient : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- With `1-3e₂ ≥ 1`, the complex place contributes `(1-3e₂)^{3/2}` to `H(P,O(3D₀))`. -/
theorem archimedean_height (hN : 1 ≤ 1 - 3 * (P linearCoefficient : ℝ)) :
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 (realPoint P) =
      (((1 - 3 * (P linearCoefficient : ℝ)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  set N := 1 - 3 * (P linearCoefficient : ℝ)
  rw [archimedean_localHeight, archimedeanAbs_norm, archimedeanAbs_cubic P _ (Or.inl rfl),
    archimedeanAbs_cubic P _ (Or.inr rfl), max_self]
  have h2 : N ^ 2 ≤ N ^ 3 := pow_le_pow_right₀ hN (by norm_num)
  have h1 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN
  rw [max_eq_right (max_le h1 h2), ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  norm_num

end Archimedean

/-! ### Assembly -/

theorem height_three (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : AffineInvariantRing.IntegralPoint P)
    (hN : 1 ≤ 1 - 3 * (P linearCoefficient : ℝ)) :
    height 3 0 (diagonal P) = (((1 - 3 * (P linearCoefficient : ℝ)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  have hint := (IntegralPointComparison.integralPoint_iff P).mp hP
  have hfin : FiniteAdelicData.inverseHeight (-3) 0 (finiteDiagonal P) = 1 := by
    unfold FiniteAdelicData.inverseHeight
    calc
      _ = ∏' _ : Nat.Primes, (1 : ℂ) := tprod_congr fun p => local_height_one p _ (hint p)
      _ = 1 := tprod_one
  simp only [height, AdelicData.inverseHeight, neg_zero]
  change ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 (baseChange ℝ P) *
    FiniteAdelicData.inverseHeight (-3) 0 (finiteDiagonal P) = _
  rw [hfin, mul_one]
  exact archimedean_height P hN

/-- `1-3e₂ ≥ 1` at an integral point: it is nonnegative since `(1-3e₂)³ = |z₊|²`, and it is an
integer congruent to one modulo three. -/
theorem norm_ge_one (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : AffineInvariantRing.IntegralPoint P) :
    1 ≤ 1 - 3 * (P linearCoefficient : ℝ) := by
  have hcube := archimedeanAbs_cubic P (2, 1) (Or.inl rfl)
  have hnonneg : 0 ≤ (1 - 3 * (P linearCoefficient : ℝ)) ^ 3 := by
    rw [← hcube, archimedeanAbs_eq]
    positivity
  have hN : 0 ≤ 1 - 3 * (P linearCoefficient : ℝ) := by
    by_contra h
    push_neg at h
    have : (1 - 3 * (P linearCoefficient : ℝ)) ^ 3 < 0 := Odd.pow_neg (by decide) h
    linarith
  obtain ⟨⟨a, ha⟩, -⟩ := (IntegralPointComparison.coefficient_criterion P).mp hP
  rw [ha] at hN ⊢
  push_cast at hN ⊢
  have : (a : ℝ) ≤ 0 := by
    have h' : (3 * a : ℤ) ≤ 1 := by exact_mod_cast (by linarith : (3 * (a : ℝ)) ≤ 1)
    exact_mod_cast (show a ≤ 0 by omega)
  linarith

theorem «prop:canonicalHeight» : CubicTargets.ToricHeights.CanonicalHeight.Claim := by
  refine ⟨fun P => ?_, fun P hP => ?_⟩
  · rw [IntegralPointComparison.coefficient_criterion P]
    exact cubic_integral_iff _ _
  · have hN := norm_ge_one P hP
    have h3 := height_three P hP hN
    rw [show (3 : ℂ) = 3 * 1 by ring, height_cube, height_eq_norm, ← Complex.ofReal_pow] at h3
    have hr := Complex.ofReal_injective h3
    rw [height_eq_norm]
    congr 1
    rw [← pow_left_inj₀ (norm_nonneg _) (Real.sqrt_nonneg _) three_ne_zero, hr,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num

end Cubic.ToricHeights.CanonicalHeight
