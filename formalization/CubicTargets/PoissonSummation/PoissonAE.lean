import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Almost-everywhere Poisson summation: `eqn:poissonae`

`BlackBox` is the general almost-everywhere Poisson summation formula for a
locally compact abelian group `G` and a countable discrete subgroup `Γ`, for a
*given* Haar measure `ν` on the dual of `G ⧸ Γ` satisfying Fourier inversion on the
quotient. It is a proposition, not proved here and not an axiom; results that use it
take `hPoisson : BlackBox` as an explicit hypothesis.
`PoissonWithDualMeasure.BlackBox` is the variant that also asserts the existence of
such a dual measure; it is the form used in the proofs of the paper's results.

The statement uses only mathlib objects. The discrete subgroup is countable, as is
the paper's rational point group; Haar measures are regular in the textbook sense.
The paper's annihilator is represented by
`PontryaginDual (G ⧸ Γ)`: a character is evaluated on `G` by composing with the
quotient map. Thus it is automatically trivial on `Γ`. Commutativity identifies
the paper's left quotient with mathlib's group quotient.

`μQ` is `μ` divided by counting measure on `Γ`, as expressed by mathlib's
fundamental-domain API. Existence of a fundamental domain is included so that
`QuotientMeasureEqMeasurePreimage` cannot be satisfied vacuously; in the adelic
application the fundamental domain is constructed.
The implication's first premise characterizes the dual measure `ν` by almost-everywhere
Fourier inversion on the quotient, exactly as in the paper's preceding exposition.

Both transforms use the inverse character; reconstruction uses the character itself.
The conclusion includes absolute convergence of the counting integral almost everywhere,
making explicit the convergence implicit in the displayed formula. It does not assert
convergence or equality at the identity. No cubic-specific scalar occurs here.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.PoissonAE

open MeasureTheory

/-- The general Poisson input recalled at `eqn:poissonae`, with its measure normalization.
This is a proposition definition, not a proof; results that use it carry it as an
explicit hypothesis. -/
def BlackBox : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] [BorelSpace (G ⧸ Γ)]
    [MeasurableSpace (PontryaginDual (G ⧸ Γ))] [BorelSpace (PontryaginDual (G ⧸ Γ))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μQ : Measure (G ⧸ Γ)) [μQ.IsHaarMeasure] [μQ.Regular]
    [HasFundamentalDomain Γ.op G μ] [QuotientMeasureEqMeasurePreimage μ μQ]
    (ν : Measure (PontryaginDual (G ⧸ Γ))) [ν.IsHaarMeasure] [ν.Regular],
    -- The paper defines the dual measure by this inversion property on the quotient.
    (∀ F : G ⧸ Γ → ℂ,
      let Fhat := fun χ : PontryaginDual (G ⧸ Γ) =>
        ∫ q : G ⧸ Γ, F q * (χ q : ℂ)⁻¹ ∂μQ
      Integrable F μQ → Integrable Fhat ν →
        ∀ᵐ q ∂μQ, F q = ∫ χ, Fhat χ * (χ q : ℂ) ∂ν) →
    -- These are the two L¹ hypotheses in the paragraph containing `eqn:poissonae`.
    ∀ f : G → ℂ,
      let fhat := fun χ : PontryaginDual (G ⧸ Γ) =>
        ∫ x : G, f x * (χ (QuotientGroup.mk x) : ℂ)⁻¹ ∂μ
      Integrable f μ → Integrable fhat ν →
        ∀ᵐ y ∂μ,
          Integrable (fun γ : Γ => f ((γ : G) * y)) Measure.count ∧
          (∫ γ : Γ, f ((γ : G) * y) ∂Measure.count) =
            ∫ χ, fhat χ * (χ (QuotientGroup.mk y) : ℂ) ∂ν

end CubicTargets.PoissonSummation.PoissonAE
