import Cubic.PoissonSummation.RationalAdelicEmbedding
import Cubic.PoissonSummation.RationalProductFormula
import Cubic.ToricHeights.QuotientNormLogarithm
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The adelic logarithm and character on rational points

Compare every original place contribution with the same independently
descended rational norm character. The rational logarithmic product formula
then proves that the assembled logarithm vanishes on the actual diagonal,
and that its exponential character is trivial there.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicRationalCharacter

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois QuotientNormCharacter
open Cubic.ToricHeights QuotientFiniteHeight QuotientNormLogarithm
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open RationalAdelicEmbedding
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

private theorem transport_logarithm_equiv_property
    {A : Type*} [Mul A]
    (P : (D : LocalData) → (D.Carrier → ℝ × ℝ) → (D.Carrier ≃* A) → Prop)
    {D F : LocalData} (h : D = F) (L : F.Carrier → ℝ × ℝ) (e : F.Carrier ≃* A)
    (he : P F L e) :
    P D ((congrArg (fun D => D.Carrier → ℝ × ℝ) h).mpr L)
      ((congrArg (fun D => D.Carrier ≃* A) h).mpr e) := by
  subst F
  exact he

/-- All finite logarithms use the original rational norm character with the same factor `-1/2`. -/
theorem local_logarithm_eq_norm (p : Nat.Primes) : ∀ x : (family p).Carrier,
    FiniteAdelicData.localLogarithm p x =
      (-Real.log ‖(value ℚ_[p] (originalEquiv p x) : ℚ_[p])‖ / 2,
       -Real.log ‖(value ℚ_[p] (originalEquiv p x) : ℚ_[p])‖ / 2) := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    simp only [FiniteAdelicData.localLogarithm, originalEquiv, dif_pos hs]
    exact transport_logarithm_equiv_property
      (fun D L e => ∀ x, L x =
        (-Real.log ‖(value ℚ_[p] (e x) : ℚ_[p])‖ / 2,
         -Real.log ‖(value ℚ_[p] (e x) : ℚ_[p])‖ / 2))
      (family_split ⟨p, hs⟩) (splitLogarithm p) (MulEquiv.refl _) (split_logarithm p)
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    simp only [FiniteAdelicData.localLogarithm, originalEquiv, dif_neg hs, dif_pos hi]
    exact transport_logarithm_equiv_property
      (fun D L e => ∀ x, L x =
        (-Real.log ‖(value ℚ_[p] (e x) : ℚ_[p])‖ / 2,
         -Real.log ‖(value ℚ_[p] (e x) : ℚ_[p])‖ / 2))
      (family_inert ⟨p, hi⟩) (inertLogarithm p) (MulEquiv.refl _) (inert_logarithm p)
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    have hp : p = primeThree := Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst p
    change ∀ x, ramifiedLogarithm x = _
    exact ramified_logarithm

/-- Naturality identifies every local norm value of a rational point with the same rational number. -/
theorem norm_baseChange (A : Type*) [CommRing A] [Algebra ℚ A] (P : Points) :
    (value A (baseChange A P) : A) = algebraMap ℚ A (value ℚ P : ℚ) := rfl

theorem local_logarithm_diagonal (p : Nat.Primes) (P : Points) :
    FiniteAdelicData.localLogarithm p (finiteDiagonal P p) =
      (-Real.log ‖((value ℚ P : ℚ) : ℚ_[p])‖ / 2,
       -Real.log ‖((value ℚ P : ℚ) : ℚ_[p])‖ / 2) := by
  rw [local_logarithm_eq_norm, finiteDiagonal_apply, originalEquiv_localPoint]
  change (-Real.log ‖(value ℚ_[p] (baseChange ℚ_[p] P) : ℚ_[p])‖ / 2,
    -Real.log ‖(value ℚ_[p] (baseChange ℚ_[p] P) : ℚ_[p])‖ / 2) = _
  simp only [norm_baseChange, eq_ratCast]

theorem finite_logarithm_diagonal (P : Points) :
    FiniteAdelicData.logarithm (finiteDiagonal P) =
      (Real.log ‖((value ℚ P : ℚ) : ℝ)‖ / 2,
       Real.log ‖((value ℚ P : ℚ) : ℝ)‖ / 2) := by
  have h := ((RationalProductFormula.hasSum_log_norm (value ℚ P) (value ℚ P).ne_zero).neg).div_const 2
  have hpair := h.prodMk h
  simp only [neg_neg] at hpair
  rw [FiniteAdelicData.logarithm]
  simp only [local_logarithm_diagonal]
  exact hpair.tsum_eq

/-- The actual adelic logarithm vanishes on every original rational quotient point. -/
theorem logarithm_diagonal (P : Points) : AdelicData.logarithm (diagonal P) = 0 := by
  change ArchimedeanQuotientLogarithm.logarithm (baseChange ℝ P) +
    FiniteAdelicData.logarithm (finiteDiagonal P) = 0
  rw [infinite_logarithm, norm_baseChange, finite_logarithm_diagonal, eq_ratCast]
  ext <;> dsimp <;> ring

/-- Rational triviality of the constructed character, proved from the product formula. -/
theorem character_diagonal (t : ℝ) (P : Points) : AdelicData.character t (diagonal P) = 1 := by
  rw [AdelicData.character_apply, logarithm_diagonal]
  simp [LocalLogarithmNormalization.spectralPairing]

/-- The quotient by the proved original rational diagonal, with its quotient topology. -/
abbrev AutomorphicQuotient := AdelicData.Points ⧸ diagonal.range

/-- The actual continuous character descended through the rational quotient. -/
def automorphicCharacter (t : ℝ) : PontryaginDual AutomorphicQuotient where
  __ := QuotientGroup.lift diagonal.range (AdelicData.character t).toMonoidHom (by
    rintro x ⟨P, rfl⟩
    exact character_diagonal t P)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk diagonal.range).continuous_iff.mpr
    (AdelicData.character t).continuous

/-- Pulling back the descended character gives the independently constructed exponential. -/
theorem automorphicCharacter_mk (t : ℝ) (x : AdelicData.Points) :
    automorphicCharacter t (QuotientGroup.mk x) = AdelicData.character t x := rfl

theorem automorphicCharacter_finite (p : Nat.Primes) (t : ℝ) (x : (family p).Carrier) :
    automorphicCharacter t (QuotientGroup.mk (AdelicData.includeFinite p x)) =
      (family p).character t x := by
  rw [automorphicCharacter_mk, AdelicData.character_includeFinite]

theorem automorphicCharacter_radial (t u : ℝ) :
    automorphicCharacter t (QuotientGroup.mk (AdelicData.radialSection u)) =
      Circle.exp (2 * Real.pi * t * u) := by
  rw [automorphicCharacter_mk, AdelicData.character_radialSection]

end Cubic.PoissonSummation.AdelicRationalCharacter
