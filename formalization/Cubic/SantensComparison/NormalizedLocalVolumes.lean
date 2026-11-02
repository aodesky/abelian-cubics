import Cubic.SantensComparison.LocalVolumeData
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

namespace Cubic.SantensComparison.NormalizedLocalVolumes

open LocalVolumeData MeasureTheory
open Cubic.ToricHeights Cubic.QuadraticCorrespondence Cubic.PoissonSummation
open Cubic.OrbitParametrization
open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct
open scoped SplitLocalModel InertLocalModel RamifiedLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

private theorem reciprocal_norm (p : Nat.Primes) : ‖(p : ℂ)⁻¹‖ < 1 := by
  rw [norm_inv, Complex.norm_natCast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

private theorem cpow_degree (p : Nat.Primes) (d : ℤ) :
    (p : ℂ) ^ (-(d : ℂ)) = ((p : ℝ) ^ (-d) : ℝ) := by
  rw [← Int.cast_neg, Complex.cpow_intCast]
  simp only [Complex.ofReal_zpow, Complex.ofReal_natCast]

theorem split_norm_degree (p : SplitPrimes) (x : SplitLocalModel.Points p.1) :
    ‖(x.1 : ℚ_[p.1]) * (x.2 : ℚ_[p.1])‖ =
      (p.1 : ℝ) ^ (-SplitLocalModel.degree p.1 x) := by
  have hd : SplitLocalModel.degree p.1 x =
      Padic.valuation (x.1 : ℚ_[p.1]) + Padic.valuation (x.2 : ℚ_[p.1]) := by
    simp [SplitLocalModel.degree, SplitLocalModel.valuation,
      CocharacterIsomorphism.fromCyclotomic, PadicMultiplicative.valuation]
    ring
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.1.ne_zero,
    Padic.norm_eq_zpow_neg_valuation x.2.ne_zero, hd, neg_add,
    zpow_add₀ (by exact_mod_cast p.1.2.ne_zero : (p.1 : ℝ) ≠ 0)]

theorem inert_norm_degree (p : InertPrimes) (x : InertLocalModel.Points p.1) :
    ‖(x : CyclotomicInertField.Extension p.1)‖ ^ 2 =
      (p.1 : ℝ) ^ (-InertLocalModel.degree p.1 x) := by
  rw [InertLocalModel.norm_eq_zpow_ord, InertLocalModel.degree_eq_two_ord,
    ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem split_integrand (p : SplitPrimes) :
    localIntegrand (SplitLocalFourier.data p) 0 1 0 =
      fun x => (splitWeight p x : ℂ) := by
  funext x
  change (SplitLocalIntegrality.coefficientLocus p.1).indicator
    (SplitLocalModel.inverseHeight p.1 0 1) x *
      ((SplitLocalModel.character p.1 0 x : Circle) : ℂ)⁻¹ = _
  rw [SplitLocalModel.character_zero]
  change _ * (1 : ℂ)⁻¹ = _
  rw [inv_one, mul_one]
  have hp : (p.1 : ℕ) ≠ 3 := by have := p.2; omega
  unfold splitWeight
  rw [SplitLocalIntegrality.coefficientLocus_eq_integralLocus _ hp]
  by_cases hx : x ∈ SplitLocalModel.integralLocus p.1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      SplitLocalModel.inverseHeight_on_cone _ _ _ _ hx, neg_one_mul,
      cpow_degree, split_norm_degree]
  · simp [Set.indicator_of_notMem hx]

theorem inert_integrand (p : InertPrimes) :
    localIntegrand (InertLocalFourier.data p) 0 1 0 =
      fun x => (inertWeight p x : ℂ) := by
  funext x
  change (InertLocalIntegrality.coefficientLocus p.1).indicator
    (InertLocalModel.inverseHeight p.1 0 1) x *
      ((InertLocalModel.character p.1 0 x : Circle) : ℂ)⁻¹ = _
  rw [InertLocalModel.character_zero]
  change _ * (1 : ℂ)⁻¹ = _
  rw [inv_one, mul_one]
  unfold inertWeight
  rw [InertLocalIntegrality.coefficientLocus_eq_integralLocus]
  by_cases hx : x ∈ InertLocalModel.integralLocus p.1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      InertLocalModel.inverseHeight_on_cone _ _ _ _ hx, neg_one_mul,
      cpow_degree, inert_norm_degree]
  · simp [Set.indicator_of_notMem hx]

/-- The convergent lattice sum at the norm weight `σ=1`. This uses local
convergence, which only needs `|p⁻¹|<1`, without a global Euler-product bound. -/
theorem split_series (p : SplitPrimes) :
    HasSum (LatticeSeries.weight p.1 1)
      ((1 + 2 * (p.1 : ℂ)⁻¹) / (1 - (p.1 : ℂ)⁻¹)^2) := by
  convert LatticeSeries.hasSum_cone ((p.1 : ℂ)⁻¹) (reciprocal_norm p.1) using 1
  funext n
  rw [LatticeSeries.weight_eq_pow]
  rw [Complex.cpow_neg_one]

theorem inert_series (p : InertPrimes) :
    HasSum (fun n : LatticeCone.InvariantConePoint => LatticeSeries.weight p.1 1 n.1)
      (1 - (p.1 : ℂ)⁻¹^2)⁻¹ := by
  convert LatticeSeries.hasSum_invariant_cone ((p.1 : ℂ)⁻¹) (reciprocal_norm p.1) using 1
  funext n
  rw [LatticeSeries.weight_eq_pow]
  rw [Complex.cpow_neg_one]

theorem split_moment (p : SplitPrimes) :
    Integrable (splitWeight p) (SplitLocalModel.measure p.1) ∧
      splitMoment p = (1 + 2 / (p.1 : ℝ)) / (1 - 1 / (p.1 : ℝ))^2 := by
  letI : Countable (Multiplicative (ℤ × ℤ)) := Multiplicative.toAdd.injective.countable
  have h := localFourier_of_valuation (SplitLocalFourier.data p)
    (SplitLocalFourier.valuationData p) LatticeCone.splitEmbedding _
    (split_series p).summable 0 1 0
    (by simpa only [spectralParameter_zero] using SplitLocalFourier.integrand_eq_lattice p 0 1 0)
  rw [(split_series p).tsum_eq] at h
  change Integrable (localIntegrand (SplitLocalFourier.data p) 0 1 0)
      (SplitLocalModel.measure p.1) ∧
    (∫ x, localIntegrand (SplitLocalFourier.data p) 0 1 0 x ∂SplitLocalModel.measure p.1) = _ at h
  rw [split_integrand] at h
  dsimp only at h
  rw [integral_complex_ofReal] at h
  refine ⟨by simpa only [Complex.ofReal_re] using h.1.re, ?_⟩
  apply Complex.ofReal_injective
  simpa only [splitMoment, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_inv, one_div, div_eq_mul_inv, one_mul] using h.2

theorem inert_moment (p : InertPrimes) :
    Integrable (inertWeight p) (InertLocalModel.measure p.1) ∧
      inertMoment p = (1 - 1 / (p.1 : ℝ)^2)⁻¹ := by
  letI : Countable (Multiplicative CocharacterLattice.invariantLattice) :=
    Multiplicative.toAdd.injective.countable
  have h := localFourier_of_valuation (InertLocalFourier.data p)
    (InertLocalFourier.valuationData p) LatticeCone.inertEmbedding _
    (inert_series p).summable 0 1 0
    (by simpa only [spectralParameter_zero] using InertLocalFourier.integrand_eq_lattice p 0 1 0)
  rw [(inert_series p).tsum_eq] at h
  change Integrable (localIntegrand (InertLocalFourier.data p) 0 1 0)
      (InertLocalModel.measure p.1) ∧
    (∫ x, localIntegrand (InertLocalFourier.data p) 0 1 0 x ∂InertLocalModel.measure p.1) = _ at h
  rw [inert_integrand] at h
  dsimp only at h
  rw [integral_complex_ofReal] at h
  refine ⟨by simpa only [Complex.ofReal_re] using h.1.re, ?_⟩
  apply Complex.ofReal_injective
  simpa only [inertMoment, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_natCast, one_div, inv_pow] using h.2

theorem ramified_integrand :
    (fun x => (ramifiedWeight x : ℂ)) =
      RamifiedLocalModel.integralLocus.indicator (fun _ => (1 : ℂ)) := by
  funext x
  unfold ramifiedWeight
  rw [RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus]
  by_cases hx : x ∈ RamifiedLocalModel.integralLocus
  · have hn := (CyclotomicRamifiedField.mem_compactUnits_iff_norm_one x).mp
      (RamifiedLocalModel.integralLocus_subset hx)
    simp [Set.indicator_of_mem hx, hn]
  · simp [Set.indicator_of_notMem hx]

theorem ramified_moment : Integrable ramifiedWeight RamifiedLocalModel.measure ∧
    ramifiedMoment = 1/6 := by
  have h := RamifiedLocalMeasure.integral_indicator
  rw [← ramified_integrand] at h
  dsimp only at h
  rw [integral_complex_ofReal] at h
  refine ⟨by simpa only [Complex.ofReal_re] using h.1.re, ?_⟩
  apply Complex.ofReal_injective
  simpa [ramifiedMoment] using h.2

end Cubic.SantensComparison.NormalizedLocalVolumes
