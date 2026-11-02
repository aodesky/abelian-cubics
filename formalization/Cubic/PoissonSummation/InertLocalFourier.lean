import Cubic.ToricHeights.InertLocalHeight
import Cubic.ToricHeights.InertLocalIntegrality
import Cubic.PoissonSummation.FiniteFourierProduct
import Cubic.QuadraticCorrespondence.CyclotomicInertResidueField

/-!
# The Fourier integral on the inert quadratic local field

Compute the actual Bochner integral with normalized Haar measure, the full
cubic support-function height, actual integrality cutoff, and unramified
spectral character. The integer-valued valuation and its compact kernel are
proved, not assumed. The comparison with the original torus and its geometric
data is still a separate prerequisite for the paper's full lemma.
-/

noncomputable section

namespace Cubic.PoissonSummation.InertLocalFourier

open MeasureTheory
open Cubic.ToricHeights
open Cubic.QuadraticCorrespondence
open Cubic.OrbitParametrization.CocharacterLattice
open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct
open scoped InertLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

/-- Concrete local data on the units of the actual inert quadratic extension. -/
def data (p : InertPrimes) : LocalData where
  Carrier := InertLocalModel.Points p.1
  maxCompact := InertLocalModel.compactUnits p.1
  compact := CyclotomicInertField.isCompact_compactUnits p.1
  open_compact := CyclotomicInertField.isOpen_compactUnits p.1
  maximal := CyclotomicInertField.compact_subgroup_le p.1
  measure := InertLocalModel.measure p.1
  normalized := InertLocalModel.measure_compactUnits p.1
  inverseHeight := InertLocalModel.inverseHeight p.1
  integralLocus := InertLocalIntegrality.coefficientLocus p.1
  measurable_integralLocus := by
    rw [InertLocalIntegrality.coefficientLocus_eq_integralLocus]
    exact InertLocalModel.measurable_integralLocus p.1
  character := InertLocalModel.character p.1
  character_zero := InertLocalModel.character_zero p.1

/-- The valuation exact sequence, with the paper's full invariant lattice. -/
def valuationData (p : InertPrimes) : LocalValuation (data p) (Multiplicative invariantLattice) where
  valuation := InertLocalModel.valuation p.1
  surjective := InertLocalModel.valuation_surjective p.1
  kernel := InertLocalModel.ker_valuation p.1

/-- The actual height and inverse character give the cone weight with
`λ = σ - πit`. Outside the integral cone the indicator vanishes. -/
theorem integrand_eq_lattice (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ) :
    localIntegrand (data p) s₀ σ t =
      (Function.extend LatticeCone.inertEmbedding
        (fun n => LatticeSeries.weight p.1 (spectralParameter σ t) n.1) 0) ∘
          (valuationData p).valuation := by
  funext x
  change (InertLocalIntegrality.coefficientLocus p.1).indicator (InertLocalModel.inverseHeight p.1 s₀ σ) x *
      ((InertLocalModel.character p.1 t x : Circle) : ℂ)⁻¹ =
    Function.extend LatticeCone.inertEmbedding
      (fun n => LatticeSeries.weight p.1 (spectralParameter σ t) n.1) 0
      (InertLocalModel.valuation p.1 x)
  rw [InertLocalIntegrality.coefficientLocus_eq_integralLocus]
  by_cases hx : x ∈ InertLocalModel.integralLocus p.1
  · let n : LatticeCone.InvariantConePoint :=
      ⟨⟨(InertLocalModel.valuation p.1 x).toAdd.val,
          (InertLocalModel.mem_integralLocus_iff_cone p.1 x).mp hx⟩,
        (InertLocalModel.valuation p.1 x).toAdd.property⟩
    have he : LatticeCone.inertEmbedding n = InertLocalModel.valuation p.1 x := rfl
    have hd : (InertLocalModel.degree p.1 x : ℂ) = (LatticeCone.degree n.1 : ℂ) := by
      exact_mod_cast (LatticeCone.degree_coe n.1).symm
    rw [Set.indicator_of_mem hx, InertLocalModel.inverseHeight_on_cone p.1 s₀ σ x hx,
      InertLocalModel.character_eq_cpow, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.1.2.ne_zero)]
    rw [← he, LatticeCone.inertEmbedding.injective.extend_apply]
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
    apply (InertLocalModel.mem_integralLocus_iff_cone p.1 x).mpr
    rw [← he]
    exact n.1.2

/-- The inert factor is the convergent Fourier integral of the constructed
quadratic local model, with no integral evaluation assumed as a hypothesis. -/
theorem integral_eq_inertFactor (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (localIntegrand (data p) s₀ σ t) (data p).measure ∧
      localFourier (data p) s₀ σ t = inertFactor p (spectralParameter σ t) := by
  letI : Countable (Multiplicative invariantLattice) := Multiplicative.toAdd.injective.countable
  have hs := LatticeSeries.hasSum_inert p (spectralParameter σ t) (by simpa using hσ)
  have h := localFourier_of_valuation (data p) (valuationData p) LatticeCone.inertEmbedding
    _ hs.summable s₀ σ t (integrand_eq_lattice p s₀ σ t)
  exact ⟨h.1, h.2.trans hs.tsum_eq⟩

/-- The exponent two is the proved residue degree of the constructed local field.
The complex-power identity uses a nonnegative real base, with no choice of a complex root. -/
theorem inertFactor_eq_residueFactor (p : InertPrimes) (z : ℂ) :
    inertFactor p z =
      (1 - (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p.1)) : ℂ) ^ (-z))⁻¹ := by
  simp only [inertFactor, CyclotomicInertField.card_residueField, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Nat.cast_ofNat, mul_neg]

/-- The actual Fourier integral in terms of the actual local residue cardinality,
with the same `λ=σ-πit` and the paper's full finite-place parameter range. -/
theorem integral_eq_residueFactor (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (localIntegrand (data p) s₀ σ t) (data p).measure ∧
      localFourier (data p) s₀ σ t =
        (1 - (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p.1)) : ℂ) ^
          (-spectralParameter σ t))⁻¹ := by
  obtain ⟨hI, hF⟩ := integral_eq_inertFactor p s₀ σ t hσ
  exact ⟨hI, hF.trans (inertFactor_eq_residueFactor p _)⟩

end Cubic.PoissonSummation.InertLocalFourier
