import Cubic.PoissonSummation.CharacterIntegral
import Cubic.PoissonSummation.AdelicFourierIntegral
import Cubic.PoissonSummation.AdelicLevelQuotient
import Cubic.PoissonSummation.AdelicFourierUnfolding
import Cubic.PoissonSummation.RealCharacter

/-!
# Support and descent of the actual automorphic Fourier transform

Level invariance kills every automorphic character nontrivial on `K^{D₀}`.
Every remaining character descends to the actual double quotient. Transport
through its proved logarithm isomorphism gives a continuous character of the
real additive group. The real-character classification then identifies exactly
the paper's logarithmic family. The topology and measure of the full dual
are treated separately from this set-theoretic support statement.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierSpectrum

open MeasureTheory
open AdelicHeightZetaData AdelicRationalCharacter AdelicLevel AdelicLevelQuotient
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData

/-- Pull an actual automorphic character back to the original adelic group. -/
def pullback (χ : PontryaginDual AutomorphicQuotient) : PontryaginDual Points where
  __ := χ.toMonoidHom.comp (QuotientGroup.mk' RationalAdelicEmbedding.diagonal.range)
  continuous_toFun := χ.continuous.comp QuotientGroup.continuous_mk

/-- The transform on the entire automorphic spectrum, not just the logarithmic family. -/
def transform (s₀ σ : ℂ) (χ : PontryaginDual AutomorphicQuotient) : ℂ :=
  characterIntegral AdelicHeightZetaData.measure (cutoffHeight s₀ σ) (pullback χ)

theorem transform_automorphicCharacter (s₀ σ : ℂ) (t : ℝ) :
    transform s₀ σ (automorphicCharacter t) = AdelicFourierIntegral.fourier s₀ σ t := rfl

/-- The paper's spectral-support assertion, using the original level subgroup. -/
theorem transform_eq_zero_of_nontrivial (s₀ σ : ℂ) (χ : PontryaginDual AutomorphicQuotient)
    (k : Points) (hk : k ∈ level) (hχ : χ (QuotientGroup.mk k) ≠ 1) :
    transform s₀ σ χ = 0 := by
  apply characterIntegral_eq_zero_of_invariant _ _ _ k _ hχ
  intro x
  rw [mul_comm]
  exact cutoffHeight_mul_level s₀ σ x k hk

theorem quotientLevel_le_ker_of_nonzero (s₀ σ : ℂ) (χ : PontryaginDual AutomorphicQuotient)
    (h : transform s₀ σ χ ≠ 0) : quotientLevel ≤ χ.toMonoidHom.ker := by
  rintro q ⟨k, hk, rfl⟩
  by_contra hn
  exact h (transform_eq_zero_of_nontrivial s₀ σ χ k hk hn)

/-- Descent is only for characters proved trivial on the specified level image. -/
def descended (χ : PontryaginDual AutomorphicQuotient)
    (hχ : quotientLevel ≤ χ.toMonoidHom.ker) : PontryaginDual DoubleQuotient where
  __ := QuotientGroup.lift quotientLevel χ.toMonoidHom hχ
  continuous_toFun := (QuotientGroup.isQuotientMap_mk quotientLevel).continuous_iff.mpr χ.continuous

@[simp]
theorem descended_projection (χ : PontryaginDual AutomorphicQuotient)
    (hχ : quotientLevel ≤ χ.toMonoidHom.ker) (q : AutomorphicQuotient) :
    descended χ hχ (quotientProjection q) = χ q := rfl

/-- The surviving character transported through the actual logarithm isomorphism. -/
def realCharacter (χ : PontryaginDual AutomorphicQuotient)
    (hχ : quotientLevel ≤ χ.toMonoidHom.ker) : PontryaginDual (Multiplicative ℝ) where
  __ := (descended χ hχ).toMonoidHom.comp logarithmEquiv.symm.toMonoidHom
  continuous_toFun := (descended χ hχ).continuous.comp logarithmEquiv.symm.continuous

theorem realCharacter_coordinate (χ : PontryaginDual AutomorphicQuotient)
    (hχ : quotientLevel ≤ χ.toMonoidHom.ker) (q : AutomorphicQuotient) :
    realCharacter χ hχ (AdelicCompactQuotient.quotientCoordinate q) = χ q := by
  change descended χ hχ (logarithmEquiv.symm
    (logarithmEquiv (quotientProjection q))) = χ q
  rw [logarithmEquiv.symm_apply_apply, descended_projection]

/-- Every character surviving level descent belongs to the actual logarithmic family. -/
theorem exists_parameter_of_level_trivial (χ : PontryaginDual AutomorphicQuotient)
    (hχ : quotientLevel ≤ χ.toMonoidHom.ker) :
    ∃ t : ℝ, χ = automorphicCharacter t := by
  obtain ⟨t, ht⟩ := RealCharacter.exists_parameter (realCharacter χ hχ)
  refine ⟨t, DFunLike.ext _ _ fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H x =>
    have he := ht (AdelicCompactQuotient.coordinate x).toAdd
    change realCharacter χ hχ (AdelicCompactQuotient.quotientCoordinate (QuotientGroup.mk x)) =
      Circle.exp (2 * Real.pi * t * AdelicLevel.realCoordinate x) at he
    rw [realCharacter_coordinate] at he
    rw [automorphicCharacter_mk, AdelicFourierUnfolding.character_eq_coordinate]
    exact he

/-- Nonzero global Fourier coefficients occur only in the paper's `χₘ` family. -/
theorem exists_parameter_of_transform_ne_zero (s₀ σ : ℂ)
    (χ : PontryaginDual AutomorphicQuotient) (h : transform s₀ σ χ ≠ 0) :
    ∃ t : ℝ, χ = automorphicCharacter t :=
  exists_parameter_of_level_trivial χ (quotientLevel_le_ker_of_nonzero s₀ σ χ h)

end Cubic.PoissonSummation.AdelicFourierSpectrum
