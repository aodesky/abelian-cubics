import Cubic.PoissonSummation.RationalPrimeGenerators

/-!
# Correcting arbitrary finite local valuations by rational points

The chosen global generators realize every valuation at their prime, including
negative valuations. Their support statements ensure the correction is compact
at every other prime. All three local assertions concern the original torus.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalPrimeCorrections

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois RationalAdelicEmbedding RationalPrimeGenerators
open Cubic.OrbitParametrization
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

variable (p : ℕ) [Fact p.Prime]

private theorem padic_order_of_norm (x : ℚ_[p]ˣ) (n : ℤ)
    (h : ‖(x : ℚ_[p])‖ = (p : ℝ) ^ (-n)) : PadicMultiplicative.valuation p x =
      Multiplicative.ofAdd n := by
  change Padic.valuation (x : ℚ_[p]) = n
  apply neg_injective
  exact (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt :
    (1 : ℝ) < p)).injective ((Padic.norm_eq_zpow_neg_valuation x.ne_zero).symm.trans h)

section Split
variable [Fact (p % 3 = 1)]

def splitParameter : Points →* SplitLocalModel.Points p :=
  (QuotientLocalModels.splitEquiv p).toMonoidHom.comp (baseChange ℚ_[p])

def firstOrder : Points →* Multiplicative ℤ :=
  (PadicMultiplicative.valuation p).comp ((MonoidHom.fst _ _).comp (splitParameter p))

def secondOrder : Points →* Multiplicative ℤ :=
  (PadicMultiplicative.valuation p).comp ((MonoidHom.snd _ _).comp (splitParameter p))

theorem firstOrder_splitPoint : firstOrder p (splitPoint p) = Multiplicative.ofAdd 1 := by
  apply padic_order_of_norm
  simpa only [Int.reduceNeg, zpow_neg_one] using splitPoint_first_norm p

theorem secondOrder_splitPoint : secondOrder p (splitPoint p) = 1 := by
  apply padic_order_of_norm p _ 0
  simpa only [neg_zero, zpow_zero] using splitPoint_second_norm p

theorem firstOrder_scalarPoint :
    firstOrder p (scalarPoint p (Fact.out : p.Prime).ne_zero) = Multiplicative.ofAdd 1 := by
  change PadicMultiplicative.valuation p
    ((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p]
      (scalarPoint p (Fact.out : p.Prime).ne_zero))).1) = _
  rw [split_scalarPoint, PadicMultiplicative.valuation_uniformizer]

theorem secondOrder_scalarPoint :
    secondOrder p (scalarPoint p (Fact.out : p.Prime).ne_zero) = Multiplicative.ofAdd 1 := by
  change PadicMultiplicative.valuation p
    ((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p]
      (scalarPoint p (Fact.out : p.Prime).ne_zero))).2) = _
  rw [split_scalarPoint, PadicMultiplicative.valuation_uniformizer]

theorem split_correction (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ∃ P : Points, P ∈ supportedAt p ∧
      (baseChange ℚ_[p] P)⁻¹ * x ∈ QuotientLocalHaar.splitCompactUnits p := by
  let y := QuotientLocalModels.splitEquiv p x
  let a := (PadicMultiplicative.valuation p y.1).toAdd
  let b := (PadicMultiplicative.valuation p y.2).toAdd
  let P := splitPoint p ^ (a - b) * scalarPoint p (Fact.out : p.Prime).ne_zero ^ b
  have h₁ : firstOrder p P = Multiplicative.ofAdd a := by
    simp only [P, map_mul, map_zpow, firstOrder_splitPoint, firstOrder_scalarPoint,
      ← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id, mul_one, ← ofAdd_add, sub_add_cancel]
  have h₂ : secondOrder p P = Multiplicative.ofAdd b := by
    simp only [P, map_mul, map_zpow, secondOrder_splitPoint, secondOrder_scalarPoint,
      one_zpow, one_mul, ← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id, mul_one]
  refine ⟨P, (supportedAt p).mul_mem
    ((supportedAt p).zpow_mem (splitPoint_supported p) _)
    ((supportedAt p).zpow_mem (scalarPoint_supported p (Fact.out : p.Prime)) _), ?_⟩
  change QuotientLocalModels.splitEquiv p ((baseChange ℚ_[p] P)⁻¹ * x) ∈
    SplitLocalModel.compactUnits p
  rw [map_mul, map_inv]
  constructor
  · rw [← PadicMultiplicative.ker_valuation]
    change PadicMultiplicative.valuation p ((splitParameter p P).1⁻¹ * y.1) = 1
    rw [map_mul, map_inv]
    change (firstOrder p P)⁻¹ * Multiplicative.ofAdd a = 1
    rw [h₁, inv_mul_cancel]
  · rw [← PadicMultiplicative.ker_valuation]
    change PadicMultiplicative.valuation p ((splitParameter p P).2⁻¹ * y.2) = 1
    rw [map_mul, map_inv]
    change (secondOrder p P)⁻¹ * Multiplicative.ofAdd b = 1
    rw [h₂, inv_mul_cancel]

end Split

theorem inert_correction [Fact (p % 3 = 2)] (x : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    ∃ P : Points, P ∈ supportedAt p ∧
      (baseChange ℚ_[p] P)⁻¹ * x ∈ QuotientLocalHaar.inertCompactUnits p := by
  let y := QuotientLocalModels.inertEquiv p x
  let n := InertLocalModel.ord p y
  let P := scalarPoint p (Fact.out : p.Prime).ne_zero ^ n
  refine ⟨P, (supportedAt p).zpow_mem (scalarPoint_supported p (Fact.out : p.Prime)) n, ?_⟩
  change QuotientLocalModels.inertEquiv p ((baseChange ℚ_[p] P)⁻¹ * x) ∈
    InertLocalModel.compactUnits p
  rw [← InertLocalModel.ker_integerValuation]
  change InertLocalModel.integerValuation p
    (QuotientLocalModels.inertEquiv p ((baseChange ℚ_[p] P)⁻¹ * x)) = 1
  simp only [P, map_mul, map_inv, map_zpow, QuotientLocalModels.inertEquiv_apply,
    inert_scalarPoint, InertLocalModel.integerValuation_uniformizer]
  change (Multiplicative.ofAdd (1 : ℤ) ^ n)⁻¹ * Multiplicative.ofAdd n = 1
  simp only [← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id, mul_one, inv_mul_cancel]

theorem ramified_correction (x : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ∃ P : Points, P ∈ supportedAt 3 ∧
      (baseChange ℚ_[3] P)⁻¹ * x ∈ QuotientLocalHaar.ramifiedCompactUnits := by
  let y := QuotientLocalModels.ramifiedEquiv x
  let n := RamifiedLocalModel.ord y
  let P := ramifiedPoint ^ n
  refine ⟨P, (supportedAt 3).zpow_mem ramifiedPoint_supported n, ?_⟩
  change QuotientLocalModels.ramifiedEquiv ((baseChange ℚ_[3] P)⁻¹ * x) ∈
    RamifiedLocalModel.compactUnits
  rw [← RamifiedLocalModel.ker_integerValuation]
  change RamifiedLocalModel.integerValuation
    (QuotientLocalModels.ramifiedEquiv ((baseChange ℚ_[3] P)⁻¹ * x)) = 1
  simp only [P, map_mul, map_inv, map_zpow, QuotientLocalModels.ramifiedEquiv_apply,
    ramifiedPoint_local]
  change (Multiplicative.ofAdd (RamifiedLocalModel.ord RamifiedLocalModel.ramifiedParameter) ^ n)⁻¹ *
    Multiplicative.ofAdd n = 1
  simp only [RamifiedLocalModel.ord_ramifiedParameter, ← ofAdd_zsmul, zsmul_eq_mul,
    Int.cast_id, mul_one, inv_mul_cancel]

end Cubic.PoissonSummation.RationalPrimeCorrections
