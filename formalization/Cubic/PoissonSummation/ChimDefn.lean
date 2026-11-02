import CubicTargets.PoissonSummation.ChimDefn
import Cubic.PoissonSummation.AdelicFourierSpectrumTopology

/-!
# Proof of `eqn:chimdefn`

The paper deduces the equation from `lemma:KprimeGroup`: a character trivial on
`K^{D₀}` factors through `T(ℚ)\T(𝔸)/K^{D₀} ≅ 𝔱`. The Lean route is the same:
`AdelicFourierSpectrum.exists_parameter_of_level_trivial` transports the character
through the proved logarithm isomorphism of the double quotient and classifies
characters of `ℝ`. Here we only translate its parameter `t` into the invariant
functional `m ∈ 𝔱^∨` with `m(v₀) = t`: an invariant functional agrees with
`spectralPairing (m v₀)` everywhere (`eq_spectralPairing`), and uniqueness of `m`
follows from injectivity of the parameter map (`parameterHom_injective`).
-/

noncomputable section

namespace Cubic.PoissonSummation.ChimDefn

open CubicTargets.PoissonSummation.ChimDefn
open Cubic.ToricHeights.LocalLogarithmNormalization
open AdelicRationalCharacter AdelicFourierSpectrum AdelicLevelQuotient
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology

/-- An invariant functional is determined by `t = m(v₀)`, and is the spectral pairing. -/
theorem eq_spectralPairing (m : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hm : m ∈ invariantDual) (n : ℝ × ℝ) :
    m n = spectralPairing (m (-1, -1)) n := by
  have hs : m (0, 1) = m (1, 0) := hm (1, 0)
  have hn : n = n.1 • ((1 : ℝ), (0 : ℝ)) + n.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hv : ((-1 : ℝ), (-1 : ℝ)) = (-1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + (-1 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, hn, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hs]
  simp only [spectralPairing, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd]
  ring

/-- The invariant functional with value `t` on `v₀`. -/
def functional (t : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (-t / 2) • (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)

theorem functional_apply (t : ℝ) (n : ℝ × ℝ) : functional t n = spectralPairing t n := by
  simp [functional, spectralPairing]
  ring

theorem functional_mem (t : ℝ) : functional t ∈ invariantDual := by
  intro n
  simp only [functional_apply, spectralPairing, Prod.fst_swap, Prod.snd_swap]
  ring

theorem isChi_automorphicCharacter (m : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hm : m ∈ invariantDual) :
    IsChi m (automorphicCharacter (m (-1, -1))) := by
  intro x
  rw [automorphicCharacter_mk, AdelicData.character_apply, eq_spectralPairing m hm (AdelicData.logarithm x)]

theorem levelTrivial_iff (χ : PontryaginDual AutomorphicQuotient) :
    LevelTrivial χ ↔ quotientLevel ≤ χ.toMonoidHom.ker := by
  constructor
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk
  · intro h k hk
    exact h ⟨k, hk, rfl⟩

theorem eq_of_isChi {m : (ℝ × ℝ) →ₗ[ℝ] ℝ} (hm : m ∈ invariantDual)
    {χ : PontryaginDual AutomorphicQuotient} (h : IsChi m χ) :
    χ = automorphicCharacter (m (-1, -1)) := by
  apply DFunLike.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x => rw [h x, isChi_automorphicCharacter m hm x]

theorem «eqn:chimdefn» : Claim where
  exists_character m hm :=
    ⟨automorphicCharacter (m (-1, -1)),
      (levelTrivial_iff _).mpr (automorphicCharacter_mem_levelAnnihilator _),
      isChi_automorphicCharacter m hm⟩
  eq_chi χ hχ := by
    obtain ⟨t, rfl⟩ := exists_parameter_of_level_trivial χ ((levelTrivial_iff χ).mp hχ)
    have hv : functional t (-1, -1) = t := by
      rw [functional_apply]; exact spectralPairing_v0 t
    refine ⟨functional t, ⟨functional_mem t, ?_⟩, ?_⟩
    · have := isChi_automorphicCharacter (functional t) (functional_mem t)
      rwa [hv] at this
    · rintro m ⟨hm, hχm⟩
      have he := eq_of_isChi hm hχm
      have ht : m (-1, -1) = t := by
        have := parameterHom_injective (a₁ := Multiplicative.ofAdd (m (-1, -1)))
          (a₂ := Multiplicative.ofAdd t) (Subtype.ext he.symm)
        simpa using this
      apply LinearMap.ext
      intro n
      rw [eq_spectralPairing m hm, ht, functional_apply]

end Cubic.PoissonSummation.ChimDefn
