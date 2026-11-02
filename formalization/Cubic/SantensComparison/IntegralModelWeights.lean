import Cubic.SantensComparison.AffineConeAlgebra
import Cubic.SantensComparison.LocalVolumeData
import Cubic.ToricHeights.QuotientInvariantIntegrality
import Cubic.ToricHeights.QuotientLocalModels

/-! Finite local densities for arbitrary integral subalgebras of the actual
quadratic torus coordinate ring. Specialization to the paper is proved from
all regular functions, before identifying the densities with the previously
computed norm moments. -/

noncomputable section

namespace Cubic.SantensComparison.IntegralModelWeights

open ToricMetricData Cubic.ToricHeights Cubic.QuadraticCorrespondence
open CyclotomicTorusGalois DescendedCoefficients DescendedCyclicInvariant
open Cubic.PoissonSummation.FiniteEulerProduct
open scoped SplitLocalModel InertLocalModel RamifiedLocalModel
open scoped RegularFunctionTopology RationalQuotientGroup

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance splitFact (p : SplitPrimes) : Fact ((p.1 : ℕ)%3=1) := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ)%3=2) := ⟨p.2⟩

def localLocus (A : IntegralModel) (p : ℕ) [Fact p.Prime] :
    Set (quotientFixedRing →ₐ[ℚ] ℚ_[p]) := {P | ∀ f ∈ A, ‖P f‖ ≤ 1}

def splitLocus (A : IntegralModel) (p : SplitPrimes) : Set (SplitLocalModel.Points p.1) :=
  (QuotientLocalModels.splitEquiv p.1).symm ⁻¹' localLocus A p.1

def inertLocus (A : IntegralModel) (p : InertPrimes) : Set (InertLocalModel.Points p.1) :=
  (QuotientLocalModels.inertEquiv p.1).symm ⁻¹' localLocus A p.1

def ramifiedLocus (A : IntegralModel) : Set RamifiedLocalModel.Points :=
  QuotientLocalModels.ramifiedEquiv.symm ⁻¹' localLocus A 3

def splitWeight (A : IntegralModel) (φ : Support) (a : ℝ) (k : ℤ) (p : SplitPrimes) :
    SplitLocalModel.Points p.1 → ℝ :=
  (splitLocus A p).indicator (fun x =>
    ‖splitHeight φ p.1 ((QuotientLocalModels.splitEquiv p.1).symm x)‖ ^ (-a) *
      ‖(x.1 : ℚ_[p.1])*(x.2 : ℚ_[p.1])‖ ^ k)

def inertWeight (A : IntegralModel) (φ : Support) (a : ℝ) (k : ℤ) (p : InertPrimes) :
    InertLocalModel.Points p.1 → ℝ :=
  (inertLocus A p).indicator (fun x =>
    ‖inertHeight φ p.1 ((QuotientLocalModels.inertEquiv p.1).symm x)‖ ^ (-a) *
      (‖(x : CyclotomicInertField.Extension p.1)‖^2) ^ k)

def ramifiedWeight (A : IntegralModel) (φ : Support) (a : ℝ) (k : ℤ) :
    RamifiedLocalModel.Points → ℝ :=
  (ramifiedLocus A).indicator (fun x =>
    ‖ramifiedHeight φ (QuotientLocalModels.ramifiedEquiv.symm x)‖ ^ (-a) *
      (‖(x : CyclotomicRamifiedField.Extension)‖^2) ^ k)

theorem paper_local_locus (p : ℕ) [Fact p.Prime] :
    localLocus paperModel p=QuotientInvariantIntegrality.invariantLocus p := by
  ext P
  change (∀ f ∈ paperModel, ‖P f‖ ≤ 1) ↔
    ‖P linearCoefficient‖ ≤ 1 ∧ ‖-P constantCoefficient‖ ≤ 1 ∧ ‖P delta‖ ≤ 1
  rw [AffineConeAlgebra.paperModel_generators, norm_neg]
  constructor
  · intro h
    exact ⟨h _ (Algebra.subset_adjoin (by simp)),h _ (Algebra.subset_adjoin (by simp)),
      h _ (Algebra.subset_adjoin (by simp))⟩
  · rintro ⟨ha,hb,hd⟩ f hf
    change P f ∈ PadicInt.subring p
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hd
    | algebraMap z => simp
    | add f g _ _ hf hg => simpa only [map_add] using (PadicInt.subring p).add_mem hf hg
    | mul f g _ _ hf hg => simpa only [map_mul] using (PadicInt.subring p).mul_mem hf hg

theorem paper_split_locus (p : SplitPrimes) :
    splitLocus paperModel p=SplitLocalIntegrality.coefficientLocus p.1 := by
  ext x
  rw [splitLocus, Set.mem_preimage, paper_local_locus,
    QuotientInvariantIntegrality.split_mem_iff]
  rw [← QuotientLocalModels.splitEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

theorem paper_inert_locus (p : InertPrimes) :
    inertLocus paperModel p=InertLocalIntegrality.coefficientLocus p.1 := by
  ext x
  rw [inertLocus, Set.mem_preimage, paper_local_locus,
    QuotientInvariantIntegrality.inert_mem_iff]
  rw [← QuotientLocalModels.inertEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

theorem paper_ramified_locus :
    ramifiedLocus paperModel=RamifiedLocalIntegrality.coefficientLocus := by
  ext x
  rw [ramifiedLocus, Set.mem_preimage, paper_local_locus,
    QuotientInvariantIntegrality.ramified_mem_iff]
  rw [← QuotientLocalModels.ramifiedEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

theorem paper_split_height (p : SplitPrimes) (x : SplitLocalModel.Points p.1)
    (hx : x ∈ SplitLocalIntegrality.coefficientLocus p.1) :
    splitHeight paperSupport p.1 ((QuotientLocalModels.splitEquiv p.1).symm x)=1 := by
  have h3 : (p.1:ℕ) ≠ 3 := by intro h; have := p.2; simp [h] at this
  rw [SplitLocalIntegrality.coefficientLocus_eq_integralLocus p.1 h3] at hx
  change QuotientFiniteHeight.splitInverseHeight p.1 (-1) 0 _=1
  rw [QuotientFiniteHeight.splitInverseHeight_eq,
    ← QuotientLocalModels.splitEquiv_apply, ContinuousMulEquiv.apply_symm_apply,
    SplitLocalModel.inverseHeight_on_cone _ _ _ _ hx]
  simp

theorem paper_inert_height (p : InertPrimes) (x : InertLocalModel.Points p.1)
    (hx : x ∈ InertLocalIntegrality.coefficientLocus p.1) :
    inertHeight paperSupport p.1 ((QuotientLocalModels.inertEquiv p.1).symm x)=1 := by
  rw [InertLocalIntegrality.coefficientLocus_eq_integralLocus] at hx
  change QuotientFiniteHeight.inertInverseHeight p.1 (-1) 0 _=1
  rw [QuotientFiniteHeight.inertInverseHeight_eq,
    ← QuotientLocalModels.inertEquiv_apply, ContinuousMulEquiv.apply_symm_apply,
    InertLocalModel.inverseHeight_on_cone _ _ _ _ hx]
  simp

theorem paper_ramified_height (x : RamifiedLocalModel.Points)
    (hx : x ∈ RamifiedLocalIntegrality.coefficientLocus) :
    ramifiedHeight paperSupport (QuotientLocalModels.ramifiedEquiv.symm x)=1 := by
  rw [RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus] at hx
  change QuotientFiniteHeight.ramifiedInverseHeight (-1) 0 _=1
  rw [QuotientFiniteHeight.ramifiedInverseHeight_eq,
    ← QuotientLocalModels.ramifiedEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
  exact RamifiedLocalModel.inverseHeight_on_compactUnits _ _ _
    (RamifiedLocalModel.integralLocus_subset hx)

theorem paper_split_weight (p : SplitPrimes) :
    splitWeight paperModel paperSupport 2 1 p=LocalVolumeData.splitWeight p := by
  ext x
  unfold splitWeight LocalVolumeData.splitWeight
  rw [paper_split_locus]
  by_cases hx : x ∈ SplitLocalIntegrality.coefficientLocus p.1
  · simp [Set.indicator_of_mem hx, paper_split_height p x hx]
  · simp [Set.indicator_of_notMem hx]

theorem paper_inert_weight (p : InertPrimes) :
    inertWeight paperModel paperSupport 2 1 p=LocalVolumeData.inertWeight p := by
  ext x
  unfold inertWeight LocalVolumeData.inertWeight
  rw [paper_inert_locus]
  by_cases hx : x ∈ InertLocalIntegrality.coefficientLocus p.1
  · simp [Set.indicator_of_mem hx, paper_inert_height p x hx]
  · simp [Set.indicator_of_notMem hx]

theorem paper_ramified_weight :
    ramifiedWeight paperModel paperSupport 2 1=LocalVolumeData.ramifiedWeight := by
  ext x
  unfold ramifiedWeight LocalVolumeData.ramifiedWeight
  rw [paper_ramified_locus]
  by_cases hx : x ∈ RamifiedLocalIntegrality.coefficientLocus
  · simp [Set.indicator_of_mem hx, paper_ramified_height x hx]
  · simp [Set.indicator_of_notMem hx]

end Cubic.SantensComparison.IntegralModelWeights
