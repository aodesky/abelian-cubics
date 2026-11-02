import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.RestrictedProductStages

/-!
# Topological and measure properties of the actual adelic group

The local point comparisons and the countable finite-place exhaustion supply
second countability. Haar invariance, regularity and sigma-finiteness then
follow for the measures constructed independently of the height integral.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicHeightZetaData

open MeasureTheory TopologicalSpace
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar

local instance unitsSecondCountable {R : Type*} [Monoid R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology Rˣ := by
  letI : SecondCountableTopology Rᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : R ≃ₜ Rᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance localSecondCountable (p : Nat.Primes) :
    SecondCountableTopology (family p).Carrier := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact (QuotientLocalModels.splitEquiv p).toHomeomorph.secondCountableTopology
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact (QuotientLocalModels.inertEquiv p).toHomeomorph.secondCountableTopology
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact QuotientLocalModels.ramifiedEquiv.toHomeomorph.secondCountableTopology

scoped instance : SecondCountableTopology FiniteAdelicData.Points :=
  RestrictedProductHaar.secondCountableTopology (fun p => (family p).Carrier)
    (fun p => (family p).maxCompact)

scoped instance : SecondCountableTopology ArchimedeanHaarData.Points :=
  CyclotomicArchimedean.pointEquiv.toHomeomorph.secondCountableTopology

scoped instance : LocallyCompactSpace ArchimedeanHaarData.Points :=
  ArchimedeanHaar.normalizationBand.locallyCompactSpace_of_group

scoped instance : T2Space ArchimedeanHaarData.Points :=
  CyclotomicArchimedean.pointEquiv.toHomeomorph.isEmbedding.t2Space

scoped instance : SigmaCompactSpace Points := sigmaCompactSpace_of_locallyCompact_secondCountable
scoped instance : SigmaCompactSpace FiniteAdelicData.Points :=
  sigmaCompactSpace_of_locallyCompact_secondCountable
scoped instance : SigmaCompactSpace ArchimedeanHaarData.Points :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

instance : finiteMeasure.IsHaarMeasure := by unfold finiteMeasure; infer_instance
instance : SigmaFinite finiteMeasure := Measure.IsHaarMeasure.sigmaFinite finiteMeasure
instance : SigmaFinite ArchimedeanHaar.measure :=
  Measure.IsHaarMeasure.sigmaFinite ArchimedeanHaar.measure
instance : SFinite ArchimedeanHaar.measure := instSFiniteOfSigmaFinite
instance : measure.IsHaarMeasure :=
  Measure.prod.instIsHaarMeasure ArchimedeanHaar.measure finiteMeasure
instance : SigmaFinite measure := Measure.IsHaarMeasure.sigmaFinite measure
instance : measure.Regular := by
  let K := ArchimedeanHaar.normalizationBand ×ˢ
    (RestrictedProductHaar.normalizationCompact (fun p => (family p).Carrier)
      (fun p => (family p).maxCompact) (fun p => (family p).open_compact)
      (fun p => (family p).compact))
  exact Measure.regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_ne_top

end Cubic.PoissonSummation.AdelicHeightZetaData
