import CubicTargets.PoissonSummation.LogarithmExactSequence

/-!
# Supporting facts for the concrete adelic logarithm sequence

Compactness and logarithmic triviality of the specified compact subgroup,
injectivity of the left map and surjectivity of the right map. The reverse
kernel inclusion is supplied by finite principalization in
`AdelicPrincipalizationConsequences`; `LogarithmExactSequence` assembles the result.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicCompactQuotient

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open QuotientFiniteFourierProduct RationalAdelicEmbedding AdelicRationalCharacter
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

theorem continuous_compactMap : Continuous compactMap := by
  apply (QuotientGroup.isQuotientMap_mk rationalCompact).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp continuous_subtype_val

theorem isCompact_maximalCompact : IsCompact (maximalCompact : Set AdelicData.Points) := by
  have harch : IsCompact
      (ArchimedeanHaar.coordinateHom.ker : Set ArchimedeanQuotientLogarithm.Points) := by
    simpa only [Set.Icc_self] using ArchimedeanHaar.isCompact_coordinate_band 0 0
  exact harch.prod (RestrictedProductHaar.isCompact_compactSubgroup
    (fun p => (family p).Carrier) (fun p => (family p).maxCompact) (fun p => (family p).compact))

theorem coordinate_eq_one_of_mem_maximalCompact {x : AdelicData.Points}
    (hx : x ∈ maximalCompact) : coordinate x = 1 := by
  have ha : ArchimedeanQuotientLogarithm.coordinate x.1 = 0 := hx.1
  have hf : FiniteAdelicData.logarithm x.2 = 0 := by
    have hlocal (p : Nat.Primes) : FiniteAdelicData.localLogarithm p (x.2 p) = 0 :=
      FiniteAdelicData.local_logarithm_zero p (x.2 p) (hx.2 p)
    simp only [FiniteAdelicData.logarithm, hlocal, tsum_zero]
  change -(AdelicData.logarithm x).1 = 0
  simp [AdelicData.logarithm, hf, ArchimedeanQuotientLogarithm.logarithm_eq, ha]

theorem compactMap_injective : Function.Injective compactMap := by
  apply (injective_iff_map_eq_one compactMap).mpr
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (QuotientGroup.eq_one_iff (x : AdelicData.Points)).mp hx

theorem compactMap_range_le_ker : compactMap.range ≤ quotientCoordinate.ker := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientGroup.induction_on with
  | H x => exact coordinate_eq_one_of_mem_maximalCompact x.property

/-- The final step of the paper's proof: the infinite place already gives surjectivity. -/
theorem quotientCoordinate_surjective : Function.Surjective quotientCoordinate := by
  intro u
  exact ⟨QuotientGroup.mk (AdelicData.radialSection u.toAdd), coordinate_radialSection u.toAdd⟩

end Cubic.PoissonSummation.AdelicCompactQuotient
