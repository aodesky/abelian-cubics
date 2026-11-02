import CubicTargets.PoissonSummation.PoissonAE

/-!
# Poisson summation with existence of the normalized dual measure

`BlackBox` is the general harmonic-analysis input used in the proofs of the paper's
results (`eqn:poissonae`). For a locally compact abelian group `G`, a countable discrete
subgroup `Γ`, a Haar measure `μ` on `G` and the quotient measure `μQ` on `G ⧸ Γ`, it asserts
that there is a regular Haar measure `ν` on the dual of `G ⧸ Γ` such that
* Fourier inversion holds for every `F ∈ L¹(μQ)` with `F̂ ∈ L¹(ν)`, almost everywhere
  (this is the normalization of the dual measure in the exposition preceding
  `eqn:poissonae`), and
* the Poisson summation formula holds almost everywhere for every `f ∈ L¹(μ)` with
  `f̂ ∈ L¹(ν)`, including absolute convergence of the sum over `Γ`.
`PoissonAE.BlackBox` is the same Poisson statement for a supplied dual measure.

All objects are standard mathlib objects. No cubic-specific subgroup, scalar,
height function or integrability assertion occurs. The application to the adelic torus
proves the quotient data, restriction of the dual measure to the relevant
spectrum, its scalar six, both `L¹` hypotheses and evaluation at zero.
The definition introduces neither an axiom nor a proof.
-/

namespace CubicTargets.PoissonSummation.PoissonWithDualMeasure

open MeasureTheory

/-- The general Poisson summation input. Results that use it take this entire
proposition as a hypothesis; it is neither proved here nor asserted as an axiom. -/
def BlackBox : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] [BorelSpace (G ⧸ Γ)]
    [MeasurableSpace (PontryaginDual (G ⧸ Γ))] [BorelSpace (PontryaginDual (G ⧸ Γ))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μQ : Measure (G ⧸ Γ)) [μQ.IsHaarMeasure] [μQ.Regular]
    [HasFundamentalDomain Γ.op G μ] [QuotientMeasureEqMeasurePreimage μ μQ],
    ∃ ν : Measure (PontryaginDual (G ⧸ Γ)), ν.IsHaarMeasure ∧ ν.Regular ∧
      (∀ F : G ⧸ Γ → ℂ,
        let Fhat := fun χ : PontryaginDual (G ⧸ Γ) =>
          ∫ q : G ⧸ Γ, F q * (χ q : ℂ)⁻¹ ∂μQ
        Integrable F μQ → Integrable Fhat ν →
          ∀ᵐ q ∂μQ, F q = ∫ χ, Fhat χ * (χ q : ℂ) ∂ν) ∧
      (∀ f : G → ℂ,
        let fhat := fun χ : PontryaginDual (G ⧸ Γ) =>
          ∫ x : G, f x * (χ (QuotientGroup.mk x) : ℂ)⁻¹ ∂μ
        Integrable f μ → Integrable fhat ν →
          ∀ᵐ y ∂μ,
            Integrable (fun γ : Γ => f ((γ : G) * y)) Measure.count ∧
            (∫ γ : Γ, f ((γ : G) * y) ∂Measure.count) =
              ∫ χ, fhat χ * (χ (QuotientGroup.mk y) : ℂ) ∂ν)

end CubicTargets.PoissonSummation.PoissonWithDualMeasure
