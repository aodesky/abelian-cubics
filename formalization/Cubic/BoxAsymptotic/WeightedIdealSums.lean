import Cubic.BoxAsymptotic.AngularMaximalSums
import Cubic.BoxAsymptotic.WeightedPartialSums

/-! Abel summation for the actual ideal sums in `lem:moment`. The unweighted
maximum is exactly the object controlled by the proved angular large sieve. -/

noncomputable section

namespace Cubic.BoxAsymptotic.WeightedIdealSums

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.IdealLargeSieve
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.AngularMaximalSums
open MeasureTheory

def coefficient (S : Finset (Ideal Integers)) (χ a : Ideal Integers → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ S.filter (fun I => Ideal.absNorm I = n), a I * χ I

theorem prefix_sum (S : Finset (Ideal Integers)) (χ a : Ideal Integers → ℂ) (q : ℕ) :
    (∑ n ∈ Finset.Icc 0 q, coefficient S χ a n) =
      ∑ I ∈ initial S q, a I * χ I := by
  classical
  simp only [coefficient]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp only [initial, Finset.mem_Icc, Nat.zero_le, true_and]

theorem coefficient_zero (χ a : Ideal Integers → ℂ) (Y : ℝ) :
    coefficient (idealBall Y) χ a 0 = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  obtain ⟨hI, h0⟩ := Finset.mem_filter.mp hI
  have hpos := norm_pos hI
  omega

theorem weighted_fibers (S : Finset (Ideal Integers)) (χ a : Ideal Integers → ℂ)
    (w : ℝ → ℂ) (E : Finset ℕ) :
    (∑ n ∈ E, w n * coefficient S χ a n) =
      ∑ I ∈ S.filter (fun I => Ideal.absNorm I ∈ E),
        w (Ideal.absNorm I) * (a I * χ I) := by
  classical
  simp only [coefficient, Finset.mul_sum]
  calc
    _ = ∑ n ∈ E, ∑ I ∈ S.filter (fun I => Ideal.absNorm I = n),
        w (Ideal.absNorm I) * (a I * χ I) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro I hI
      rw [(Finset.mem_filter.mp hI).2]
    _ = _ := Finset.sum_fiberwise_eq_sum_filter _ _ _ _

def initialWeighted (χ a : Ideal Integers → ℂ) (Y : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ I ∈ idealBall Y, w (Ideal.absNorm I) * (a I * χ I)

def intervalWeighted (χ a : Ideal Integers → ℂ) (X Y : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ I ∈ (idealBall Y).filter (fun I => X < (Ideal.absNorm I : ℝ)),
    w (Ideal.absNorm I) * (a I * χ I)

theorem initial_fibers (χ a : Ideal Integers → ℂ) (Y : ℝ) (w : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, w n * coefficient (idealBall Y) χ a n) =
      initialWeighted χ a Y w := by
  rw [weighted_fibers]
  unfold initialWeighted
  congr 1
  apply Finset.filter_eq_self.mpr
  intro I hI
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (mem_idealBall.mp hI).2⟩

theorem interval_fibers (χ a : Ideal Integers → ℂ) {X Y : ℝ}
    (hX : 0 ≤ X) (w : ℝ → ℂ) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, w n * coefficient (idealBall Y) χ a n) =
      intervalWeighted χ a X Y w := by
  classical
  rw [weighted_fibers]
  unfold intervalWeighted
  congr 1
  ext I
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hI, hX', _⟩
    exact ⟨hI, (Nat.floor_lt hX).mp hX'⟩
  · rintro ⟨hI, hX'⟩
    exact ⟨hI, (Nat.floor_lt hX).mpr hX', Nat.le_floor (mem_idealBall.mp hI).2⟩

theorem initial_bound (χ a : Ideal Integers → ℂ) {Y : ℝ} {w : ℝ → ℂ}
    (hwd : ∀ x ∈ Set.Icc 1 Y, DifferentiableAt ℝ w x)
    (hwi : IntegrableOn (deriv w) (Set.Icc 1 Y)) :
    ‖initialWeighted χ a Y w‖ ≤
      maximal χ a Y * (‖w Y‖ + ∫ x in Set.Ioc 1 Y, ‖deriv w x‖) := by
  rw [← initial_fibers]
  exact WeightedPartialSums.initial_bound (coefficient (idealBall Y) χ a)
    (coefficient_zero χ a Y) hwd hwi (fun q hq => by
      rw [prefix_sum]
      exact partial_le_maximal χ a Y hq)

theorem interval_bound (χ a : Ideal Integers → ℂ) {X Y : ℝ} {w : ℝ → ℂ}
    (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hwd : ∀ x ∈ Set.Icc X Y, DifferentiableAt ℝ w x)
    (hwi : IntegrableOn (deriv w) (Set.Icc X Y)) :
    ‖intervalWeighted χ a X Y w‖ ≤
      maximal χ a Y * (‖w Y‖ + ‖w X‖ + ∫ x in Set.Ioc X Y, ‖deriv w x‖) := by
  rw [← interval_fibers χ a hX]
  exact WeightedPartialSums.interval_bound (coefficient (idealBall Y) χ a) hX hXY
    hwd hwi (fun q hq => by
      rw [prefix_sum]
      exact partial_le_maximal χ a Y hq)

end Cubic.BoxAsymptotic.WeightedIdealSums
