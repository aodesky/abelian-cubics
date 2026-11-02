import Cubic.PoissonSummation.AdelicFourierSpectrum

/-!
# Topology of the surviving automorphic characters

The annihilator is a closed subgroup of the actual automorphic Pontryagin
dual. The paper's logarithmic characters give a topological group isomorphism
from the real line to this subgroup. This verifies the topology required for
the subsequent dual-Haar normalization; no dual-measure formula is assumed.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierSpectrum

open AdelicRationalCharacter AdelicLevelQuotient
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData

/-- Exactly the characters trivial on the paper's prescribed level image. -/
def levelAnnihilator : Subgroup (PontryaginDual AutomorphicQuotient) where
  carrier χ := quotientLevel ≤ χ.toMonoidHom.ker
  one_mem' := by intro q _; rfl
  mul_mem' := by
    intro χ ψ hχ hψ q hq
    change χ q * ψ q = 1
    rw [show χ q = 1 from hχ hq, show ψ q = 1 from hψ hq, one_mul]
  inv_mem' := by
    intro χ hχ q hq
    change (χ q)⁻¹ = 1
    rw [show χ q = 1 from hχ hq, inv_one]

theorem isClosed_levelAnnihilator :
    IsClosed (levelAnnihilator : Set (PontryaginDual AutomorphicQuotient)) := by
  change IsClosed {χ : PontryaginDual AutomorphicQuotient |
    ∀ q, q ∈ quotientLevel → χ q = 1}
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun q => isClosed_iInter fun _ => ?_
  exact isClosed_eq (show Continuous (fun χ : AutomorphicQuotient →ₜ* Circle => χ q)
    from continuous_eval_const q) continuous_const

instance : LocallyCompactSpace levelAnnihilator := isClosed_levelAnnihilator.locallyCompactSpace

instance : T2Space levelAnnihilator := inferInstance

instance : BaireSpace levelAnnihilator :=
  @BaireSpace.of_t2Space_locallyCompactSpace levelAnnihilator _ T2Space.r1Space _

private def coordinateHom : AutomorphicQuotient →ₜ* Multiplicative ℝ where
  __ := AdelicCompactQuotient.quotientCoordinate
  continuous_toFun := AdelicCompactQuotient.continuous_quotientCoordinate

theorem automorphicCharacter_eq_map (t : ℝ) :
    automorphicCharacter t = PontryaginDual.map coordinateHom (RealCharacter.character t) := by
  apply DFunLike.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [automorphicCharacter_mk, AdelicFourierUnfolding.character_eq_coordinate]
    rfl

theorem automorphicCharacter_mem_levelAnnihilator (t : ℝ) :
    automorphicCharacter t ∈ levelAnnihilator := by
  intro q hq
  rw [automorphicCharacter_eq_map]
  change RealCharacter.character t (AdelicCompactQuotient.quotientCoordinate q) = 1
  rw [show AdelicCompactQuotient.quotientCoordinate q = 1 from quotientLevel_le_ker hq]
  exact map_one _

/-- The character family valued in its actual closed subgroup. -/
def parameterHom : Multiplicative ℝ →ₜ* levelAnnihilator where
  toFun t := ⟨automorphicCharacter t.toAdd, automorphicCharacter_mem_levelAnnihilator t.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change automorphicCharacter 0 = 1
    rw [automorphicCharacter_eq_map]
    exact map_one ((PontryaginDual.map coordinateHom).comp RealCharacter.characterHom)
  map_mul' t v := by
    apply Subtype.ext
    simp only [automorphicCharacter_eq_map]
    exact map_mul ((PontryaginDual.map coordinateHom).comp RealCharacter.characterHom) t v
  continuous_toFun := Continuous.subtype_mk
    (show Continuous (fun t : Multiplicative ℝ => automorphicCharacter t.toAdd) from by
      simp only [automorphicCharacter_eq_map]
      exact (PontryaginDual.map coordinateHom).continuous.comp RealCharacter.continuous_character) _

theorem parameterHom_injective : Function.Injective parameterHom := by
  intro t v h
  apply RealCharacter.character_injective
  apply DFunLike.ext
  intro u
  have he := congrArg (fun χ : levelAnnihilator => (χ : PontryaginDual AutomorphicQuotient)
    (QuotientGroup.mk (AdelicData.radialSection u.toAdd))) h
  change automorphicCharacter t.toAdd _ = automorphicCharacter v.toAdd _ at he
  rw [automorphicCharacter_eq_map, automorphicCharacter_eq_map] at he
  change RealCharacter.character t.toAdd
      (AdelicCompactQuotient.quotientCoordinate (QuotientGroup.mk
        (AdelicData.radialSection u.toAdd))) = RealCharacter.character v.toAdd
      (AdelicCompactQuotient.quotientCoordinate (QuotientGroup.mk
        (AdelicData.radialSection u.toAdd))) at he
  rw [AdelicCompactQuotient.quotientCoordinate_mk,
    AdelicCompactQuotient.coordinate_radialSection] at he
  exact he

theorem parameterHom_surjective : Function.Surjective parameterHom := by
  intro χ
  obtain ⟨t, ht⟩ := exists_parameter_of_level_trivial χ χ.property
  exact ⟨Multiplicative.ofAdd t, Subtype.ext ht.symm⟩

/-- The surviving part of the full automorphic spectrum has its genuine
compact-open topology, transported by the paper's `2π` parameter. -/
def parameterEquiv : Multiplicative ℝ ≃ₜ* levelAnnihilator := by
  let e : Multiplicative ℝ ≃* levelAnnihilator :=
    MulEquiv.ofBijective parameterHom.toMonoidHom
      ⟨parameterHom_injective, parameterHom_surjective⟩
  let h := e.toEquiv.toHomeomorphOfContinuousOpen parameterHom.continuous
    (parameterHom.toMonoidHom.isOpenMap_of_sigmaCompact parameterHom_surjective
      parameterHom.continuous)
  exact { e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

@[simp]
theorem parameterEquiv_apply (t : Multiplicative ℝ) :
    (parameterEquiv t : PontryaginDual AutomorphicQuotient) =
      automorphicCharacter t.toAdd := rfl

end Cubic.PoissonSummation.AdelicFourierSpectrum
