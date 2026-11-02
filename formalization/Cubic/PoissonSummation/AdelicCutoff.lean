import Cubic.PoissonSummation.AdelicHaar
import Cubic.PoissonSummation.AdelicHeightLaws

/-!
# The actual finite integral cutoff

Outside three the cutoff is one on the maximal compact. This is the fact that
allows the paper to compute the height integral on each finite-place stage.
The exceptional prime must be included in every stage used in that argument.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicHeightZetaData

open MeasureTheory Set
open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData

theorem local_compact_subset_integral (p : Nat.Primes) (hp : p ≠ primeThree) :
    (family p).maxCompact ≤ (family p).integralLocus := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    intro x hx
    change x ∈ QuotientInvariantIntegrality.invariantLocus p
    rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus,
      QuotientLocalIntegrality.split_mem_iff,
      SplitLocalIntegrality.coefficientLocus_eq_integralLocus p (by
        intro h; exact hp (Subtype.ext h))]
    have hv : SplitLocalModel.valuation p (SplitQuotientLogarithm.localPoint p x) = 1 := by
      change SplitQuotientLogarithm.localPoint p x ∈ (SplitLocalModel.valuation p).ker
      rw [SplitLocalModel.ker_valuation]
      exact hx
    simp [SplitLocalModel.integralLocus, hv, LatticeCone.InCone]
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    intro x hx
    change x ∈ QuotientInvariantIntegrality.invariantLocus p
    rw [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus,
      QuotientLocalIntegrality.inert_mem_iff,
      InertLocalIntegrality.coefficientLocus_eq_integralLocus,
      InertLocalModel.mem_integralLocus_iff_cone]
    have hv : InertLocalModel.valuation p (InertQuotientLogarithm.localPoint p x) = 1 := by
      change InertQuotientLogarithm.localPoint p x ∈ (InertLocalModel.valuation p).ker
      rw [InertLocalModel.ker_valuation]
      exact hx
    simp [hv, LatticeCone.InCone]
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    exact (hp (Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)))).elim

def localCutoffHeight (p : Nat.Primes) (s₀ σ : ℂ) : (family p).Carrier → ℂ :=
  (family p).integralLocus.indicator ((family p).inverseHeight s₀ σ)

def finiteCutoffHeight (s₀ σ : ℂ) : FiniteAdelicData.Points → ℂ :=
  finiteIntegralLocus.indicator (FiniteAdelicData.inverseHeight s₀ σ)

theorem localCutoffHeight_one (p : Nat.Primes) (hp : p ≠ primeThree)
    (s₀ σ : ℂ) (x : (family p).Carrier) (hx : x ∈ (family p).maxCompact) :
    localCutoffHeight p s₀ σ x = 1 := by
  rw [localCutoffHeight, Set.indicator_of_mem (local_compact_subset_integral p hp hx)]
  exact FiniteAdelicData.local_height_one p s₀ σ x hx

theorem measurableSet_finiteIntegralLocus : MeasurableSet finiteIntegralLocus := by
  have h : finiteIntegralLocus = ⋂ p, (fun x : FiniteAdelicData.Points => x p) ⁻¹'
      (family p).integralLocus := by ext x; simp [finiteIntegralLocus]
  rw [h]
  exact MeasurableSet.iInter fun p => (family p).measurable_integralLocus.preimage
    (RestrictedProduct.continuous_eval p).measurable

theorem measurableSet_integralLocus : MeasurableSet integralLocus :=
  measurableSet_finiteIntegralLocus.preimage measurable_snd

theorem measurable_finiteCutoffHeight (s₀ σ : ℂ) : Measurable (finiteCutoffHeight s₀ σ) :=
  (FiniteAdelicData.continuous_inverseHeight s₀ σ).measurable.indicator
    measurableSet_finiteIntegralLocus

theorem measurable_cutoffHeight (s₀ σ : ℂ) : Measurable (cutoffHeight s₀ σ) :=
  (AdelicData.continuous_inverseHeight s₀ σ).measurable.indicator measurableSet_integralLocus

theorem cutoffHeight_eq_components (s₀ σ : ℂ) (x : Points) :
    cutoffHeight s₀ σ x = ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x.1 *
      finiteCutoffHeight s₀ σ x.2 := by
  classical
  by_cases hx : x.2 ∈ finiteIntegralLocus
  · simp [cutoffHeight, integralLocus, finiteCutoffHeight, hx, AdelicData.inverseHeight]
  · simp [cutoffHeight, integralLocus, finiteCutoffHeight, hx]

theorem norm_localCutoffHeight (p : Nat.Primes) (s₀ σ : ℂ) (x : (family p).Carrier) :
    (‖localCutoffHeight p s₀ σ x‖ : ℂ) = localCutoffHeight p s₀.re σ.re x := by
  classical
  by_cases hx : x ∈ (family p).integralLocus
  · simp only [localCutoffHeight, Set.indicator_of_mem hx, AdelicHeightLaws.local_norm_inverseHeight]
  · simp only [localCutoffHeight, Set.indicator_of_notMem hx, norm_zero, Complex.ofReal_zero]

theorem norm_finiteCutoffHeight (s₀ σ : ℂ) (x : FiniteAdelicData.Points) :
    (‖finiteCutoffHeight s₀ σ x‖ : ℂ) = finiteCutoffHeight s₀.re σ.re x := by
  classical
  by_cases hx : x ∈ finiteIntegralLocus
  · simp only [finiteCutoffHeight, Set.indicator_of_mem hx, AdelicHeightLaws.finite_norm_inverseHeight]
  · simp only [finiteCutoffHeight, Set.indicator_of_notMem hx, norm_zero, Complex.ofReal_zero]

end Cubic.PoissonSummation.AdelicHeightZetaData
