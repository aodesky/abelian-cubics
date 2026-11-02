import Cubic.PoissonSummation.AdelicLevelMeasure
import Cubic.PoissonSummation.AdelicCompactLogarithm

/-!
# The paper's representatives and their measure

The region `a(ℝ)K^{D₀}` is the entire infinite factor times the finite level.
Its rational translates are disjoint and its coordinate measure is `du/6`.
Coverage follows from the class-number argument in `PrimePrincipalization`;
`AdelicQuotientMeasure.fundamentalDomain` assembles the fundamental-domain proof.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevel

open MeasureTheory Set
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicCompactQuotient AdelicHeightZetaData RationalAdelicEmbedding
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  RestrictedProductHaar ArchimedeanHaarData AdelicHeightZetaData ENNReal

/-- The paper's region; coverage is proved separately using finite principalization. -/
def representativeRegion : Set AdelicData.Points := univ ×ˢ (finiteLevel : Set FiniteAdelicData.Points)

theorem isOpen_representativeRegion : IsOpen representativeRegion :=
  isOpen_univ.prod isOpen_finiteLevel

theorem mem_representativeRegion_iff (x : AdelicData.Points) :
    x ∈ representativeRegion ↔ ∃ u : ℝ, ∃ k : level, x = AdelicData.radialSection u * k := by
  constructor
  · intro hx
    let u := ArchimedeanQuotientLogarithm.coordinate x.1
    have hk : (AdelicData.radialSection u)⁻¹ * x ∈ level := by
      constructor
      · change ArchimedeanHaar.coordinateHom
          ((ArchimedeanQuotientLogarithm.radialSection u)⁻¹ * x.1) = 1
        rw [map_mul, map_inv]
        change -ArchimedeanQuotientLogarithm.coordinate
          (ArchimedeanQuotientLogarithm.radialSection u) +
            ArchimedeanQuotientLogarithm.coordinate x.1 = 0
        rw [ArchimedeanQuotientLogarithm.coordinate_radialSection]
        exact neg_add_cancel _
      · simpa only [AdelicData.radialSection, AdelicData.includeInfinite,
          Prod.snd_mul, Prod.snd_inv, inv_one, one_mul] using hx.2
    exact ⟨u, ⟨_, hk⟩, (mul_inv_cancel_left _ _).symm⟩
  · rintro ⟨u, k, rfl⟩
    exact ⟨mem_univ _, by simpa only [AdelicData.radialSection, AdelicData.includeInfinite,
      Prod.snd_mul, one_mul] using k.property.2⟩

def realCoordinate (x : AdelicData.Points) : ℝ := (coordinate x).toAdd

theorem coordinate_eq_infinite {x : AdelicData.Points} (hx : x.2 ∈ finiteCompact) :
    realCoordinate x = ArchimedeanQuotientLogarithm.coordinate x.1 := by
  have hf : FiniteAdelicData.logarithm x.2 = 0 := by
    have hlocal (p : Nat.Primes) : FiniteAdelicData.localLogarithm p (x.2 p) = 0 :=
      FiniteAdelicData.local_logarithm_zero p (x.2 p) (hx p)
    simp only [FiniteAdelicData.logarithm, hlocal, tsum_zero]
  change -(AdelicData.logarithm x).1 = _
  simp [AdelicData.logarithm, hf, ArchimedeanQuotientLogarithm.logarithm_eq]

theorem restrict_representativeRegion : measure.restrict representativeRegion =
    ArchimedeanHaar.measure.prod (finiteMeasure.restrict finiteLevel) := by
  rw [← Measure.restrict_univ (μ := ArchimedeanHaar.measure), Measure.prod_restrict]
  rfl

/-- The normalization on the proposed representatives is derived from the actual product measure. -/
theorem map_representativeRegion_coordinate :
    (measure.restrict representativeRegion).map realCoordinate = (1 / 6 : ℝ≥0∞) • volume := by
  have he : realCoordinate =ᵐ[measure.restrict representativeRegion]
      ArchimedeanQuotientLogarithm.coordinate ∘ Prod.fst := by
    filter_upwards [ae_restrict_mem isOpen_representativeRegion.measurableSet] with x hx
    exact coordinate_eq_infinite hx.2.1
  rw [Measure.map_congr he, ← Measure.map_map
    ArchimedeanQuotientLogarithm.continuous_coordinate.measurable measurable_fst,
    restrict_representativeRegion, Measure.map_fst_prod, Measure.restrict_apply_univ,
    finiteMeasure_level, Measure.map_smul, ArchimedeanHaar.map_measure]

/-- A rational coset has at most one representative; finite principalization supplies existence. -/
theorem quotient_injOn_representativeRegion :
    InjOn (QuotientGroup.mk : AdelicData.Points → AdelicRationalCharacter.AutomorphicQuotient)
      representativeRegion := by
  intro x hx y hy hxy
  obtain ⟨P, hP⟩ := QuotientGroup.eq.mp hxy
  have hfin : finiteDiagonal P ∈ finiteLevel := by
    have h := finiteLevel.mul_mem (finiteLevel.inv_mem hx.2) hy.2
    have he := congrArg Prod.snd hP
    change finiteDiagonal P = x.2⁻¹ * y.2 at he
    rwa [← he] at h
  have hP1 := (finiteDiagonal_mem_level_iff P).mp hfin
  rw [hP1, map_one] at hP
  exact inv_mul_eq_one.mp hP.symm

end Cubic.PoissonSummation.AdelicLevel
