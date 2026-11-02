import Cubic.PoissonSummation.AdelicRationalTopology
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Consequences of finite principalization

This file retains an explicit `FinitePrincipalization` premise and traces how
it supplies the reverse inclusion in `prop:Lmap`, the covering
property in `lemma:KprimeGroup`, and the fundamental domain used for unfolding.
`PrimePrincipalization.finitePrincipalization` discharges this premise in the
final exact-sequence and convergence proofs.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicPrincipalizationConsequences

open MeasureTheory Set
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicCompactQuotient AdelicLevel RationalAdelicEmbedding AdelicRationalCharacter
open CubicTargets.PoissonSummation.LogarithmExactSequence
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicRationalTopology

theorem exact_of_finitePrincipalization (h : FinitePrincipalization) :
    compactMap.range = quotientCoordinate.ker := by
  apply le_antisymm compactMap_range_le_ker
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨P, hP⟩ := h x.2
    let y := (diagonal P)⁻¹ * x
    have hcoord : coordinate y = 1 := by
      change coordinate ((diagonal P)⁻¹ * x) = 1
      rw [map_mul, map_inv, (rational_le_ker ⟨P, rfl⟩ : coordinate (diagonal P) = 1)]
      simpa only [inv_one, one_mul] using hx
    have hy : y ∈ maximalCompact := by
      refine ⟨?_, hP⟩
      change ArchimedeanQuotientLogarithm.coordinate y.1 = 0
      rw [← coordinate_eq_infinite hP]
      exact congrArg Multiplicative.toAdd hcoord
    refine ⟨QuotientGroup.mk (⟨y, hy⟩ : maximalCompact), ?_⟩
    change QuotientGroup.mk y = (QuotientGroup.mk x : AutomorphicQuotient)
    apply QuotientGroup.eq.mpr
    refine ⟨P, ?_⟩
    dsimp [y]
    simp [mul_comm]

theorem logarithmExactSequence_of_finitePrincipalization (h : FinitePrincipalization) : Claim :=
  ⟨compactMap_injective, exact_of_finitePrincipalization h, quotientCoordinate_surjective⟩

theorem covers_of_finitePrincipalization (h : FinitePrincipalization) (x : AdelicData.Points) :
    ∃ P : Points, (diagonal P)⁻¹ * x ∈ representativeRegion := by
  obtain ⟨P, hP⟩ := h x.2
  obtain ⟨u, hu⟩ := exists_finite_unit_correction ⟨(finiteDiagonal P)⁻¹ * x.2, hP⟩
  refine ⟨P * RationalUnitReduction.rationalUnit u, mem_univ _, ?_⟩
  change (finiteDiagonal (P * RationalUnitReduction.rationalUnit u))⁻¹ * x.2 ∈ finiteLevel
  simpa only [map_mul, mul_inv_rev, mul_assoc] using hu

/-- The paper's proposed region is a fundamental domain once its arithmetic covering is proved. -/
theorem fundamentalDomain_of_finitePrincipalization (h : FinitePrincipalization) :
    IsFundamentalDomain diagonal.range representativeRegion AdelicHeightZetaData.measure := by
  apply IsFundamentalDomain.mk' isOpen_representativeRegion.measurableSet.nullMeasurableSet
  intro x
  obtain ⟨P, hP⟩ := covers_of_finitePrincipalization h x
  refine ⟨⟨(diagonal P)⁻¹, diagonal.range.inv_mem ⟨P, rfl⟩⟩, hP, ?_⟩
  intro g hg
  apply Subtype.ext
  apply mul_right_cancel (b := x)
  apply quotient_injOn_representativeRegion hg hP
  have hg0 : (QuotientGroup.mk (g : AdelicData.Points) : AutomorphicQuotient) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr g.property
  have hP0 : (QuotientGroup.mk ((diagonal P)⁻¹) : AutomorphicQuotient) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (diagonal.range.inv_mem ⟨P, rfl⟩)
  change (QuotientGroup.mk ((g : AdelicData.Points) * x) : AutomorphicQuotient) =
    QuotientGroup.mk ((diagonal P)⁻¹ * x)
  simp only [QuotientGroup.mk_mul, hg0, hP0, one_mul]

end Cubic.PoissonSummation.AdelicPrincipalizationConsequences
