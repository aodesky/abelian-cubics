import Cubic.BoxAsymptotic.IdealAngularData
import Cubic.BoxAsymptotic.MaximalLatticeSieve

/-! Transfer of the maximal lattice sieve to actual integral ideals. Each
ideal is represented by its chosen generator, whose norm is proved equal to
the ideal norm. No Euler product or analytic character hypothesis is used. -/

noncomputable section

namespace Cubic.BoxAsymptotic.IdealLargeSieve

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.EisensteinCoordinates
open Cubic.BoxAsymptotic.LatticeSums Cubic.BoxAsymptotic.BinaryRayEnergy
open CubicTargets.BoxAsymptotic

def initial (S : Finset (Ideal Integers)) (q : ℕ) : Finset (Ideal Integers) :=
  S.filter (fun I => Ideal.absNorm I ≤ q)

theorem norm_pos {Y : ℝ} {I : Ideal Integers} (hI : I ∈ idealBall Y) :
    1 ≤ Ideal.absNorm I := by
  have h0 := (mem_idealBall.mp hI).1
  have hn : Ideal.absNorm I ≠ 0 := by
    intro hn
    exact h0 (Ideal.absNorm_eq_zero_iff.mp hn)
  omega

theorem point_ball {Y : ℝ} {S : Finset (Ideal Integers)} (hS : S ⊆ idealBall Y) :
    S.image point ⊆ ball Y := by
  intro p hp
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨h0, hY⟩ := mem_idealBall.mp (hS hI)
  exact mem_ball.mpr ⟨point_ne_zero h0, by simpa only [real_norm_point] using hY⟩

theorem restrict_image {Y : ℝ} {S : Finset (Ideal Integers)}
    (hS : S ⊆ idealBall Y) (q : ℕ) :
    restrict (S.image point) (Finset.Icc 1 q) = (initial S q).image point := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hpS
    rw [norm_point, Finset.mem_Icc] at hpq
    exact Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨hI, hpq.2⟩, rfl⟩
  · intro hp
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hI, hq⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨I, hI, rfl⟩,
      by rw [norm_point]; exact Finset.mem_Icc.mpr ⟨norm_pos (hS hI), hq⟩⟩

theorem sum_initial {Y : ℝ} {S : Finset (Ideal Integers)} (hS : S ⊆ idealBall Y)
    (a : Ideal Integers → ℂ) (q : ℕ) (k : ℤ) :
    (∑ p ∈ restrict (S.image point) (Finset.Icc 1 q),
      a (spanCoord p) * phase k (eis p)) =
      ∑ I ∈ initial S q, a I * generatorPhase k I := by
  classical
  rw [restrict_image hS, Finset.sum_image point_injective.injOn]
  apply Finset.sum_congr rfl
  intro I hI
  rw [span_point, generatorPhase_eq k (mem_idealBall.mp (hS (Finset.mem_filter.mp hI).1)).1]

theorem maximal_bound
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (M : ℤ) (Y : ℝ), 2 ≤ Y →
      ∀ (S : Finset (Ideal Integers)), S ⊆ idealBall Y →
      ∀ (a : Ideal Integers → ℂ),
        (∀ I ∈ S, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
        ∀ (q : Fin N → ℕ), (∀ n, q n ≤ ⌊Y⌋₊) →
      (∑ n : Fin N, ‖∑ I ∈ initial S (q n),
        a I * generatorPhase (M + (n : ℤ) + 1) I‖ ^ 2) ≤
        C * ((N : ℝ) + Y) * Real.log (2 * Y) ^ 5 := by
  classical
  obtain ⟨C, hC, hbound⟩ := MaximalLatticeSieve.maximal_bound hLS hRM
  refine ⟨C, hC, fun N hN M Y hY S hS a ha q hq => ?_⟩
  have ha' : ∀ p ∈ S.image point, ‖a (spanCoord p)‖ ≤ 1 / Real.sqrt (nrm p) := by
    intro p hp
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hp
    simpa only [span_point, real_norm_point] using ha I hI
  have h := hbound N hN M Y hY (S.image point) (point_ball hS)
    (fun p => a (spanCoord p)) ha' q hq
  simpa only [sum_initial hS a] using h

end Cubic.BoxAsymptotic.IdealLargeSieve
