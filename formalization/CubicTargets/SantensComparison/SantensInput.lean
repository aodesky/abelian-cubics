import Cubic.SantensComparison.ToricCountingData
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! Named literature input, not an axiom or an instantiated counting theorem.

Source: T. Santens, arXiv:2312.13914v2, Theorem 8.7, with the constant
comparison of Theorem 6.9 and Lemma 5.24. This is the rank-two,
permutation-Picard case on Res_{Q(sqrt(-3))/Q} Gm, expressed through fan,
semigroup-algebra and canonical-metric data. The fan and integral model
are arbitrary; the current paper's count and constant do not occur here.

The reduction of the source to this form uses the toric character-divisor
presentation, Lemma 3.9, the Hochschild--Serre comparison in Lemma 3.24,
and the vanishing of H1 of a permutation lattice. The latter is independently
proved for the actual absolute Galois action in PermutationCohomology.
Construction 4.25 and Lemma 4.27 identify the Haar normalizations; the
ramified normalization is fixed by the logarithmic-differential integral
on 1+3O. The sole real face has the standard circle residue chart.
Finite generation, the generic-fibre comparison and the proper fan support
give the compact open integral weights by proper pullback and spreading out.

The corrected convergence factors are L*(1,Pic U) times the inverse local
Artin factors, as required by the cancellation in Lemma 5.20. The torsor
integrals are over the quotient by the rational Neron--Severi torus, as in
Theorem 6.9. The opposite signs in the two boundary maps of Lemma 3.9 are
also retained. These corrections to the printed displays are explicit.

A theorem using this input is conditional on the cited literature package.
Its specialization still has to prove every displayed hypothesis and
identify both the original counting function and all the local integrals.
-/

namespace CubicTargets.SantensComparison.SantensInput

open Cubic.SantensComparison
open ToricPairData ToricPicardData ToricMetricData ToricCountingData
open Filter Asymptotics

def GeneralSantens : Prop :=
  ∀ (P : Pair) (L : Lattices P) (A : IntegralModel) (φ : Support) (a : ℝ) (k : ℤ),
    P.Applicability A φ → L.Pointed →
    (∃ m : ℤ × ℤ, L.heightClass φ=((m.1:ℝ),(m.2:ℝ))) →
    0 < a → Lattices.Anticanonical P φ a k →
    0 < coefficient L A φ a k →
      (∀ B : ℝ, (boundedPoints A φ B).Finite) ∧
        (fun B : ℝ => (count A φ B : ℝ)) ~[atTop]
          (fun B : ℝ => coefficient L A φ a k * B ^ a * Real.log B)

end CubicTargets.SantensComparison.SantensInput
