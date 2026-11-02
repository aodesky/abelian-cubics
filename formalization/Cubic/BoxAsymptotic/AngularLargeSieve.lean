import CubicTargets.BoxAsymptotic.AngularLargeSieve
import Cubic.BoxAsymptotic.AngularMaximalSums
import Cubic.BoxAsymptotic.HeckeGeneratorPhases

/-! Full proof of `lem:angularLargeSieve`, conditional only on the explicitly
cited additive large sieve and pointwise binary decomposition inequality.

We keep all chosen generator rays rather than quotienting them by units.
Their full angles are separated, so the ordinary sieve bounds all consecutive
integer frequencies. Restricting afterward to a residue class gives the paper's
sum with the same order of magnitude. This avoids extra residue-dependent
unit factors; the logarithmic powers and the binary-cutoff step are unchanged.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularLargeSieve

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.AngularMomentData
open Cubic.BoxAsymptotic.AngularMaximalSums
open CubicTargets.BoxAsymptotic

theorem «lem:angularLargeSieve»
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    AngularLargeSieveClaim := by
  obtain ⟨C, hC, hb⟩ := generator_bound hLS hRM
  refine ⟨C, hC, fun K Y hK hY r _hr a ha => ?_⟩
  have hsub : residueModes K r ⊆ positiveModes K := Finset.filter_subset _ _
  have hg (b : Ideal Integers → ℂ)
      (hb' : ∀ I ∈ idealBall Y, ‖b I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) :
      (∑ k ∈ residueModes K r, maximal (generatorPhase k) b Y ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      (hb K Y hK hY b hb')
  have hpsi (b : Ideal Integers → ℂ)
      (hb' : ∀ I ∈ idealBall Y, ‖b I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) :
      (∑ k ∈ residueModes K r, maximal (psi k) b Y ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5 := by
    simp_rw [maximal_away]
    exact hg (away b) (fun I hI => (norm_away_le b I).trans (hb' I hI))
  have hac : ∀ I ∈ idealBall Y, ‖conjugate a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I) := by
    intro I hI
    simpa only [conjugate, norm_star] using ha I hI
  refine ⟨hpsi a ha, ?_, ?_⟩
  · simpa only [maximal_conjugate] using hpsi (conjugate a) hac
  · intro hr
    have he (k : ℤ) (hk : k ∈ residueModes K r) : primitivePsi k = generatorPhase k := by
      have hd : 6 ∣ k := Int.dvd_of_emod_eq_zero (by
        simpa only [hr] using (Finset.mem_filter.mp hk).2)
      exact funext (fun I => by simp only [primitivePsi, if_pos hd])
    constructor
    · calc
        _ = ∑ k ∈ residueModes K r, maximal (generatorPhase k) a Y ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [he k hk]
        _ ≤ _ := hg a ha
    · simp_rw [maximal_conjugate]
      calc
        _ = ∑ k ∈ residueModes K r, maximal (generatorPhase k) (conjugate a) Y ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [he k hk]
        _ ≤ _ := hg (conjugate a) hac

end Cubic.BoxAsymptotic.AngularLargeSieve
