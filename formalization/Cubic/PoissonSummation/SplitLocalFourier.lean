import Cubic.ToricHeights.SplitLocalIntegrality
import Cubic.PoissonSummation.FiniteFourierProduct

/-!
# The Fourier integral of the concrete split coordinate model

This computes an actual integral on `ℚ_[p]ˣ × ℚ_[p]ˣ`, with its normalized Haar
measure, the cubic support-function height, coefficient-integrality cutoff, and
spectral character. The equivalence with the valuation-cone cutoff is proved.
The cyclotomic tensor splitting is proved in `CyclotomicLocalTopology.lean`.
The remaining comparison with the paper's `T(ℚ_p)` includes the torus isomorphism
and its compatibility with height, integral locus and character; these are
supplied in `QuotientLocalFourier`.
-/

noncomputable section

namespace Cubic.PoissonSummation.SplitLocalFourier

open MeasureTheory
open Cubic.ToricHeights
open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct
open scoped SplitLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

private theorem prime_ne_three (p : SplitPrimes) : (p.1 : ℕ) ≠ 3 := by
  have := p.2
  omega

/-- Concrete local data for the split p-adic coordinate model. -/
def data (p : SplitPrimes) : LocalData where
  Carrier := SplitLocalModel.Points p.1
  maxCompact := SplitLocalModel.compactUnits p.1
  compact := SplitLocalModel.isCompact_compactUnits p.1
  open_compact := SplitLocalModel.isOpen_compactUnits p.1
  maximal := SplitLocalModel.compact_subgroup_le p.1
  measure := SplitLocalModel.measure p.1
  normalized := SplitLocalModel.measure_compactUnits p.1
  inverseHeight := SplitLocalModel.inverseHeight p.1
  integralLocus := SplitLocalIntegrality.coefficientLocus p.1
  measurable_integralLocus := by
    rw [SplitLocalIntegrality.coefficientLocus_eq_integralLocus _ (prime_ne_three p)]
    exact SplitLocalModel.measurable_integralLocus p.1
  character := SplitLocalModel.character p.1
  character_zero := SplitLocalModel.character_zero p.1

/-- The required exact sequence is now constructed for this concrete model. -/
def valuationData (p : SplitPrimes) : LocalValuation (data p) (Multiplicative (ℤ × ℤ)) where
  valuation := SplitLocalModel.valuation p.1
  surjective := SplitLocalModel.valuation_surjective p.1
  kernel := SplitLocalModel.ker_valuation p.1

/-- The height, cutoff and inverse character give precisely the stated cone
weight, for all parameters. This verifies the spectral shift and sign. -/
theorem integrand_eq_lattice (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ) :
    localIntegrand (data p) s₀ σ t =
      (Function.extend LatticeCone.splitEmbedding
        (LatticeSeries.weight p.1 (spectralParameter σ t)) 0) ∘ (valuationData p).valuation := by
  funext x
  change (SplitLocalIntegrality.coefficientLocus p.1).indicator (SplitLocalModel.inverseHeight p.1 s₀ σ) x *
      ((SplitLocalModel.character p.1 t x : Circle) : ℂ)⁻¹ =
    Function.extend LatticeCone.splitEmbedding (LatticeSeries.weight p.1 (spectralParameter σ t)) 0
      (SplitLocalModel.valuation p.1 x)
  rw [SplitLocalIntegrality.coefficientLocus_eq_integralLocus _ (prime_ne_three p)]
  by_cases hx : x ∈ SplitLocalModel.integralLocus p.1
  · let n : LatticeCone.ConePoint := ⟨(SplitLocalModel.valuation p.1 x).toAdd, hx⟩
    have he : LatticeCone.splitEmbedding n = SplitLocalModel.valuation p.1 x := rfl
    have hd : (SplitLocalModel.degree p.1 x : ℂ) = (LatticeCone.degree n : ℂ) := by
      exact_mod_cast (LatticeCone.degree_coe n).symm
    rw [Set.indicator_of_mem hx, SplitLocalModel.inverseHeight_on_cone p.1 s₀ σ x hx,
      SplitLocalModel.character_eq_cpow, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.1.2.ne_zero)]
    rw [← he, LatticeCone.splitEmbedding.injective.extend_apply]
    unfold LatticeSeries.weight
    rw [hd]
    congr 1
    simp only [spectralParameter]
    ring
  · rw [Set.indicator_of_notMem hx, zero_mul]
    symm
    apply Function.extend_apply'
    rintro ⟨n, he⟩
    apply hx
    change LatticeCone.InCone (SplitLocalModel.valuation p.1 x).toAdd
    rw [← he]
    exact n.2

/-- The split factor is the convergent Fourier integral of the concrete p-adic
coordinate model. The arithmetic comparison with the original torus is separate. -/
theorem integral_eq_splitFactor (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (localIntegrand (data p) s₀ σ t) (data p).measure ∧
      localFourier (data p) s₀ σ t = splitFactor p (spectralParameter σ t) := by
  letI : Countable (Multiplicative (ℤ × ℤ)) := Multiplicative.toAdd.injective.countable
  have hs := LatticeSeries.hasSum_split p (spectralParameter σ t) (by simpa using hσ)
  have h := localFourier_of_valuation (data p) (valuationData p) LatticeCone.splitEmbedding
    _ hs.summable s₀ σ t (integrand_eq_lattice p s₀ σ t)
  exact ⟨h.1, h.2.trans hs.tsum_eq⟩

end Cubic.PoissonSummation.SplitLocalFourier
