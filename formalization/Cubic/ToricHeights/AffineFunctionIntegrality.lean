import Cubic.ToricHeights.AffineIntegralModel
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Affine polynomial functions are integral over the original cubic coefficients

The original cover coordinates satisfy their monic trace-one cubic. Therefore
every integer polynomial in them is integral over the coefficient algebra.
Injectivity of the inclusion of invariant functions reflects this integrality
back to the quotient ring. Specializing integral coefficients then forces
rational values of all these functions to be integers.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineFunctionIntegrality

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois DescendedCoefficients
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CyclicGroupAlgebra
open AffineIntegralModel Polynomial

def coefficientAlgebra : Subalgebra ℤ quotientFixedRing :=
  Algebra.adjoin ℤ {linearCoefficient, constantCoefficient}

-- Cache the standard inherited structures for this twice-nested subalgebra.
local instance : Ring coefficientAlgebra := coefficientAlgebra.toRing
local instance : CommRing coefficientAlgebra := coefficientAlgebra.toCommRing

def linearElement : coefficientAlgebra := ⟨linearCoefficient, Algebra.subset_adjoin (by simp)⟩
def constantElement : coefficientAlgebra := ⟨constantCoefficient, Algebra.subset_adjoin (by simp)⟩

def monicCubic : Polynomial coefficientAlgebra :=
  let t : Polynomial coefficientAlgebra := Polynomial.X
  t ^ 3 - t ^ 2 + Polynomial.C (R := coefficientAlgebra) linearElement * t +
    Polynomial.C (R := coefficientAlgebra) constantElement

theorem monicCubic_monic : monicCubic.Monic := by
  have h : monicCubic = X ^ 3 + (-X ^ 2 + C linearElement * X + C constantElement) := by
    dsimp [monicCubic]
    ring
  rw [h]
  apply monic_X_pow_add
  compute_degree!

theorem coverCoordinate_integral (i : ZMod 3) :
    IsIntegral coefficientAlgebra (coverCoordinate i) := by
  refine ⟨monicCubic, monicCubic_monic, ?_⟩
  have ht := trace_one CoverRing universalCover
  change coverCoordinate 0 + coverCoordinate 1 + coverCoordinate 2 = 1 at ht
  have hz : coverCoordinate 2 = 1 - coverCoordinate 0 - coverCoordinate 1 := by
    linear_combination ht
  simp only [monicCubic, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
  change coverCoordinate i ^ 3 - coverCoordinate i ^ 2 +
    coverLinearCoefficient * coverCoordinate i + coverConstantCoefficient = 0
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hi with rfl | rfl | rfl <;>
    simp only [coverLinearCoefficient, coverConstantCoefficient, secondCoeff,
      Cubic.OrbitParametrization.constantCoeff, hz] <;>
    ring

theorem affineCover_integral (f : CoverRing) (hf : f ∈ affineCoverFunctions) :
    IsIntegral coefficientAlgebra f := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf => obtain ⟨i, rfl⟩ := hf; exact coverCoordinate_integral i
  | algebraMap z =>
    have hz : IsIntegral ℤ (algebraMap ℤ CoverRing z) := isIntegral_algebraMap
    exact hz.tower_top (A := coefficientAlgebra)
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem affineFunction_integral (f : affineFunctions) :
    IsIntegral coefficientAlgebra (f.val : quotientFixedRing) := by
  apply (isIntegral_algebraMap_iff (A := quotientFixedRing) (B := CoverRing)
    Subtype.val_injective).mp
  exact affineCover_integral _ f.property

theorem coefficient_values (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ))
    (f : coefficientAlgebra) : ∃ z : ℤ, P f.val = (z : ℚ) := by
  obtain ⟨f, hf⟩ := f
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hb
  | algebraMap z => exact ⟨z, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, by simp [hm, hn]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m * n, by simp [hm, hn]⟩

def integerValue (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ)) (f : coefficientAlgebra) : ℤ :=
  Classical.choose (coefficient_values P ha hb f)

@[simp]
theorem integerValue_cast (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ)) (f : coefficientAlgebra) :
    (integerValue P ha hb f : ℚ) = P f.val :=
  (Classical.choose_spec (coefficient_values P ha hb f)).symm

/-- Specialization of the coefficient algebra lands in the integers. -/
def integerSpecialization (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ)) : coefficientAlgebra →+* ℤ where
  toFun := integerValue P ha hb
  map_zero' := by apply Int.cast_injective (α := ℚ); simp
  map_one' := by apply Int.cast_injective (α := ℚ); simp
  map_add' f g := by apply Int.cast_injective (α := ℚ); simp
  map_mul' f g := by apply Int.cast_injective (α := ℚ); simp

theorem integerSpecialization_commutes (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ)) :
    (algebraMap ℤ ℚ).comp (integerSpecialization P ha hb) =
      P.toRingHom.comp (algebraMap coefficientAlgebra quotientFixedRing) := by
  apply RingHom.ext
  intro f
  exact integerValue_cast P ha hb f

/-- Every invariant integer-polynomial restriction is integer valued at integral coefficients. -/
theorem integralPoint_of_coefficients (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (ha : ∃ a : ℤ, P linearCoefficient = (a : ℚ))
    (hb : ∃ b : ℤ, P constantCoefficient = (b : ℚ)) : IntegralPoint P := by
  intro f
  have hi : IsIntegral ℤ (P f.val) :=
    IsIntegral.map_of_comp_eq (integerSpecialization P ha hb) P.toRingHom
      (integerSpecialization_commutes P ha hb) (affineFunction_integral f)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  exact ⟨z, hz.symm⟩

end Cubic.ToricHeights.AffineFunctionIntegrality
