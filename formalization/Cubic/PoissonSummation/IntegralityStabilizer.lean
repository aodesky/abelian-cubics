import Cubic.PoissonSummation.AdelicLevel
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedResidueField

/-!
# The local and global `D₀`-integrality indicators and their stabilizers

The objects named in the paper immediately before `prop:localIntegrality`.

* `localIndicatorAt p` is `1_p^{D₀}` on `T(ℚ_p)`: the indicator of the points on which the
  three original regular functions `e₂`, `e₃`, `δ` are `p`-adically integral
  (`QuotientInvariantIntegrality.invariantLocus`). `localIndicator p` is the same function on
  the carrier of the adelic factor `family p`, whose `integralLocus` field is that locus in each
  of its three branches (see `QuotientLocalFourier.splitData`, `inertData`, `ramifiedData`).
* `translationStabilizer K f` is the subgroup of `K` fixing `f` under translation; it is not
  defined by any formula for the answer. `localStabilizer p` is `K_p^{D₀}`.
* `globalIndicator` is `1^{D₀} = ⊗_v 1_v^{D₀}` with `1_∞^{D₀} = 1`, literally as the product of
  the archimedean factor and the infinite product of the finite local indicators.
* `productStabilizer` is `K^{D₀} = ∏_v K_v^{D₀}` with `K_∞^{D₀} = K_∞^{max}`, and
  `globalStabilizer` is the stabilizer of `1^{D₀}` in `K^{max}`.
* `ramifiedCongruenceSet` is `K_{3,2} = ι₃⁻¹(1+𝔴²)`. Here `ι₃` is the paper's
  `T(ℚ₃) ≅ (E ⊗ ℚ₃)^×` (`quotientRestrictionScalarsEquiv`) followed by the specified place
  `E ⊗ ℚ₃ ≅ E_w` (`RamifiedQuotientLogarithm.place`, sending `ζ ⊗ 1` to the distinguished root);
  their composite is `RamifiedQuotientLogarithm.localPoint`. `O_{E,w}` is the closed unit ball
  `CyclotomicRamifiedField.integers` and `𝔴` is its maximal ideal.
-/

noncomputable section

namespace Cubic.PoissonSummation.IntegralityStabilizer

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois QuotientFiniteFourierProduct FiniteEulerProduct
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

/-- The subgroup of `K` fixing `f` under translation. -/
def translationStabilizer {G α : Type*} [Group G] (K : Subgroup G) (f : G → α) : Subgroup G where
  carrier := {k | k ∈ K ∧ ∀ x, f (x * k) = f x}
  one_mem' := ⟨K.one_mem, fun x => by rw [mul_one]⟩
  mul_mem' := by
    rintro k l ⟨hk, hfk⟩ ⟨hl, hfl⟩
    refine ⟨K.mul_mem hk hl, fun x => ?_⟩
    rw [← mul_assoc, hfl, hfk]
  inv_mem' := by
    rintro k ⟨hk, hfk⟩
    refine ⟨K.inv_mem hk, fun x => ?_⟩
    rw [← hfk (x * k⁻¹), mul_assoc, inv_mul_cancel, mul_one]

theorem mem_translationStabilizer {G α : Type*} [Group G] (K : Subgroup G) (f : G → α) (k : G) :
    k ∈ translationStabilizer K f ↔ k ∈ K ∧ ∀ x, f (x * k) = f x := Iff.rfl

/-- `1_p^{D₀}` on the original points `T(ℚ_p)`. -/
def localIndicatorAt (p : ℕ) [Fact p.Prime] : (quotientFixedRing →ₐ[ℚ] ℚ_[p]) → ℝ :=
  (QuotientInvariantIntegrality.invariantLocus p).indicator 1

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- `1_p^{D₀}` on the carrier of the `p`-th factor of the finite restricted product. -/
def localIndicator (p : Nat.Primes) : (family p).Carrier → ℝ :=
  (family p).integralLocus.indicator 1

/-- `K_p^{D₀}`: the subgroup of `K_p^{max}` fixing `1_p^{D₀}`. -/
def localStabilizer (p : Nat.Primes) : Subgroup (family p).Carrier :=
  translationStabilizer (family p).maxCompact (localIndicator p)

/-- `K_∞^{max}`, the archimedean factor of `AdelicCompactQuotient.maximalCompact`. -/
abbrev archimedeanMaxCompact : Subgroup ArchimedeanQuotientLogarithm.Points :=
  ArchimedeanHaar.coordinateHom.ker

/-- The archimedean factor `1_∞^{D₀} = 1`. -/
def archimedeanIndicator : ArchimedeanQuotientLogarithm.Points → ℝ := fun _ => 1

/-- `1^{D₀} = ⊗_v 1_v^{D₀}` on `T(𝔸)`. -/
def globalIndicator (x : AdelicData.Points) : ℝ :=
  archimedeanIndicator x.1 * ∏' p : Nat.Primes, localIndicator p (x.2 p)

/-- `K^{D₀} = ∏_v K_v^{D₀}`, with `K_∞^{D₀} = K_∞^{max}`. -/
def productStabilizer : Subgroup AdelicData.Points where
  carrier := {x | x.1 ∈ archimedeanMaxCompact ∧ ∀ p, x.2 p ∈ localStabilizer p}
  one_mem' := ⟨archimedeanMaxCompact.one_mem, fun p => (localStabilizer p).one_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hxp⟩ ⟨hy, hyp⟩
    exact ⟨archimedeanMaxCompact.mul_mem hx hy, fun p => (localStabilizer p).mul_mem (hxp p) (hyp p)⟩
  inv_mem' := by
    rintro x ⟨hx, hxp⟩
    exact ⟨archimedeanMaxCompact.inv_mem hx, fun p => (localStabilizer p).inv_mem (hxp p)⟩

/-- The subgroup of `K^{max}` fixing `1^{D₀}`. -/
def globalStabilizer : Subgroup AdelicData.Points :=
  translationStabilizer AdelicCompactQuotient.maximalCompact globalIndicator

open CyclotomicRamifiedField (Extension integers) in
/-- `K_{3,2} = ι₃⁻¹(1+𝔴²)`, with `𝔴` the maximal ideal of `O_{E,w}`. -/
def ramifiedCongruenceSet : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3]) :=
  {P | ∃ a : integers, a ∈ IsLocalRing.maximalIdeal integers ^ 2 ∧
    ((RamifiedQuotientLogarithm.localPoint P : Extensionˣ) : Extension) = 1 + (a : Extension)}

end Cubic.PoissonSummation.IntegralityStabilizer
