import Cubic.PoissonSummation.FiniteEulerProduct
import Cubic.PoissonSummation.CharacterIntegral
import Cubic.PoissonSummation.LatticeSeries
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# General interface supporting `lemma:finiteFourierProduct`

This file contains the reusable local-data interface. The concrete paper target
is `CubicTargets.PoissonSummation.AdelicFiniteFourierProduct.Claim`.

All conclusions are stated before proof work. The left-hand side is a product of
actual Bochner integrals, not defined to equal the proposed Euler product.
`QuotientFiniteFourierProduct` supplies a proved instance on the original
descended quotient points, using character valuations, residue-weighted local
heights, original invariant cutoffs and normalized Haar measure.
`AdelicFourierComponents` identifies this family with the constructed adelic
height and descended automorphic-character components.
No theorem claims that arbitrary `LocalData` satisfy `Claim`.

`s₀` is retained as a parameter: the asserted product is independent of it. The
paper restricts to `s₁ = s₂ = σ`. The inverse/conjugate character convention is
the one used by the paper and by the external Pontryagin library.

The analytic clauses mention actual convergence; neither `tprod` nor a totalized
Bochner integral is treated as evidence that a product or integral converges.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.FiniteFourierProduct

open MeasureTheory
open Cubic.PoissonSummation.FiniteEulerProduct

/-- Analytic clauses for the exact explicit product in `lemma:finiteFourierProduct`.
The proofs are assembled in `Cubic.PoissonSummation.finiteEulerProduct_analytic`.
This structure declaration itself is a proposition, not a proof of its fields. -/
structure AnalyticClaim : Prop where
  /-- Absolute convergence in the usual Euler-factor-deviation sense. -/
  absolute_split : ∀ z : ℂ, 1 < z.re → Summable (fun p : SplitPrimes => ‖splitFactor p z - 1‖)
  absolute_inert : ∀ z : ℂ, 1 < z.re → Summable (fun q : InertPrimes => ‖inertFactor q z - 1‖)
  /-- Explicit existence of the two infinite products. -/
  convergent_split : ∀ z : ℂ, 1 < z.re → Multipliable (fun p : SplitPrimes => splitFactor p z)
  convergent_inert : ∀ z : ℂ, 1 < z.re → Multipliable (fun q : InertPrimes => inertFactor q z)
  /-- Convergence of each constituent product, locally uniformly on the full open half-plane. -/
  locally_uniform_split : HasProdLocallyUniformlyOn splitFactor
    (fun z => ∏' p : SplitPrimes, splitFactor p z) {z : ℂ | 1 < z.re}
  locally_uniform_inert : HasProdLocallyUniformlyOn inertFactor
    (fun z => ∏' q : InertPrimes, inertFactor q z) {z : ℂ | 1 < z.re}
  /-- Uniform boundedness on every closed half-plane strictly to the right of one. -/
  half_plane_bound : ∀ τ : ℝ, 1 < τ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, τ ≤ z.re → ‖value z‖ ≤ C

/-- Interface for the local objects appearing in the paper. The original-point
instance is supplied in `QuotientLocalFourier`; these fields do not assert the Fourier formula. -/
structure LocalData where
  Carrier : Type
  [group : CommGroup Carrier]
  [topology : TopologicalSpace Carrier]
  [topologicalGroup : IsTopologicalGroup Carrier]
  [locallyCompact : LocallyCompactSpace Carrier]
  [hausdorff : T2Space Carrier]
  [measurable : MeasurableSpace Carrier]
  [borel : BorelSpace Carrier]
  maxCompact : Subgroup Carrier
  compact : IsCompact (maxCompact : Set Carrier)
  open_compact : IsOpen (maxCompact : Set Carrier)
  maximal : ∀ K : Subgroup Carrier, IsCompact (K : Set Carrier) → K ≤ maxCompact
  measure : Measure Carrier
  [haar : measure.IsHaarMeasure]
  normalized : measure (maxCompact : Set Carrier) = 1
  /-- `H_p(x, -(s₀, σ, σ))`, before the integrality cutoff. -/
  inverseHeight : ℂ → ℂ → Carrier → ℂ
  integralLocus : Set Carrier
  measurable_integralLocus : MeasurableSet integralLocus
  /-- The local component of `χ_m`, with `t = m(v₀)`. -/
  character : ℝ → PontryaginDual Carrier
  /-- The revised paper's trivial character `χ₀` is the parameter value `t=0`. -/
  character_zero : character 0 = 1

attribute [instance] LocalData.group LocalData.topology LocalData.topologicalGroup
  LocalData.locallyCompact LocalData.hausdorff LocalData.measurable LocalData.borel LocalData.haar

/-- The local integrand from the paper, with the inverse unitary character. -/
def localIntegrand (D : LocalData) (s₀ σ : ℂ) (t : ℝ) (x : D.Carrier) : ℂ :=
  D.integralLocus.indicator (D.inverseHeight s₀ σ) x *
    ((D.character t x : Circle) : ℂ)⁻¹

/-- The actual local integral, distinct from the candidate Euler factor. -/
def localFourier (D : LocalData) (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  Cubic.PoissonSummation.characterIntegral D.measure
    (D.integralLocus.indicator (D.inverseHeight s₀ σ)) (D.character t)

/-- Families of local objects; the original-point family is constructed separately. -/
abbrev LocalFamily := Nat.Primes → LocalData

/-- The finite Fourier part as defined immediately before the paper's lemma. -/
def finiteFourier (D : LocalFamily) (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  ∏' p : Nat.Primes, localFourier (D p) s₀ σ t

/-- The full conclusion and convergence obligations, parameterized by local data.

The concrete paper target binds the independently constructed adelic data.
Proving this generic interface for an unrelated instance does not prove the lemma.
The integrability field records the prerequisite supplied in the paper by
`prop:heightFourierTransform`; it is not silently assumed.
-/
structure Claim (D : LocalFamily) : Prop where
  local_integrable : ∀ (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Integrable (localIntegrand (D p) s₀ σ t) (D p).measure
  finite_convergent : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Multipliable (fun p : Nat.Primes => localFourier (D p) s₀ σ t)
  /-- `eqn:finiteSpectralProduct`, with the coefficient `1/6` inside `value`. -/
  spectral_product : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    finiteFourier D s₀ σ t = value (spectralParameter σ t)
  /-- The trivial-character value at real parameters is real and nonnegative. -/
  trivial_value_real : ∀ (s₀ : ℂ) (σ : ℝ), 1 < σ →
    (finiteFourier D s₀.re σ 0).im = 0 ∧ 0 ≤ (finiteFourier D s₀.re σ 0).re
  /-- `eqn:finiteEulerBound`: the right-hand character is `χ₀`, hence `t=0`.
  Finiteness is backed by `finite_convergent`. -/
  domination : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    ‖finiteFourier D s₀ σ t‖ ≤ (finiteFourier D s₀.re σ.re 0).re
  analytic : AnalyticClaim

/-- Local calculations sufficient to assemble the full conclusion.

For the paper's canonical data these must follow from `prop:heightFourierTransform`
and `prop:localIntegrality`, including the Haar normalization at 3. No instance for
the paper is supplied here. This is an explicit prerequisite, not a replacement
definition of the local Fourier transform.
-/
structure LocalCalculation (D : LocalFamily) : Prop where
  integrable : ∀ (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Integrable (localIntegrand (D p) s₀ σ t) (D p).measure
  split : ∀ (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    localFourier (D p.1) s₀ σ t = splitFactor p (spectralParameter σ t)
  inert : ∀ (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    localFourier (D p.1) s₀ σ t = inertFactor p (spectralParameter σ t)
  at_three : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    localFourier (D primeThree) s₀ σ t = 1 / 6

/-- The remaining local geometric and measure-theoretic prerequisites.

Away from 3, these identify the actual integrals with the explicit lattice sums
from `prop:heightFourierTransform`, including the spectral height weight. At 3,
the integrand must be the unit indicator of an index-six subgroup of the
normalized maximal compact. Evaluations of these sums and of that indicator
integral are proved separately; none is a definition of the Fourier transform.
The original-point and adelic identifications are supplied in separate modules.
-/
structure LocalLatticeExpansion (D : LocalFamily) : Prop where
  integrable : ∀ (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Integrable (localIntegrand (D p) s₀ σ t) (D p).measure
  split : ∀ (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    localFourier (D p.1) s₀ σ t =
      ∑' n : Cubic.PoissonSummation.LatticeCone.ConePoint,
        Cubic.PoissonSummation.LatticeSeries.weight p.1 (spectralParameter σ t) n
  inert : ∀ (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    localFourier (D p.1) s₀ σ t =
      ∑' n : Cubic.PoissonSummation.LatticeCone.InvariantConePoint,
        Cubic.PoissonSummation.LatticeSeries.weight p.1 (spectralParameter σ t) n.1
  at_three : ∃ H : Subgroup (D primeThree).maxCompact,
    MeasurableSet (H : Set (D primeThree).maxCompact) ∧ H.index = 6 ∧
    ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
      localIntegrand (D primeThree) s₀ σ t =
        (Subtype.val '' (H : Set (D primeThree).maxCompact)).indicator (fun _ => (1 : ℂ))

/-- The finite-place exact sequence needed from `prop:basicfacts`. The target is
the full valuation lattice, including points outside the integrality cone. -/
structure LocalValuation (D : LocalData) (Γ : Type) [Group Γ] where
  valuation : D.Carrier →* Γ
  surjective : Function.Surjective valuation
  kernel : valuation.ker = D.maxCompact

/-- Geometric prerequisites for Lemma 5, with no integral evaluation or
integrability assumed. Away from 3, identify the valuation exact sequence and
the pointwise height/character integrand on its quotient. The extension by zero
records the integral locus, using the actual cone inclusions into the full
split and invariant lattices. At 3, identify the congruence subgroup and support.

The generic measure-theory argument then proves `LocalLatticeExpansion`.
The original local data and their comparisons are supplied in separate modules.
-/
structure LocalValuationDescription (D : LocalFamily) : Prop where
  split : ∀ p : SplitPrimes,
    ∃ V : LocalValuation (D p.1) (Multiplicative (ℤ × ℤ)),
      ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
        localIntegrand (D p.1) s₀ σ t =
          (Function.extend Cubic.PoissonSummation.LatticeCone.splitEmbedding
            (Cubic.PoissonSummation.LatticeSeries.weight p.1 (spectralParameter σ t)) 0) ∘
            V.valuation
  inert : ∀ p : InertPrimes,
    ∃ V : LocalValuation (D p.1)
      (Multiplicative Cubic.OrbitParametrization.CocharacterLattice.invariantLattice),
      ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
        localIntegrand (D p.1) s₀ σ t =
          (Function.extend Cubic.PoissonSummation.LatticeCone.inertEmbedding
            (fun n => Cubic.PoissonSummation.LatticeSeries.weight p.1
              (spectralParameter σ t) n.1) 0) ∘ V.valuation
  at_three : ∃ H : Subgroup (D primeThree).maxCompact,
    MeasurableSet (H : Set (D primeThree).maxCompact) ∧ H.index = 6 ∧
    ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
      localIntegrand (D primeThree) s₀ σ t =
        (Subtype.val '' (H : Set (D primeThree).maxCompact)).indicator (fun _ => (1 : ℂ))

end CubicTargets.PoissonSummation.FiniteFourierProduct
