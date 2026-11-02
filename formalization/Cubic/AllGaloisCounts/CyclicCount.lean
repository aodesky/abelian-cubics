import Cubic.AllGaloisCounts.CountData

/-! Reuse the completed cyclic count with exactly the appendix's count set
and polynomial. This supplies one branch of the all-Galois theorem. -/

namespace Cubic.AllGaloisCounts.CyclicCount
open CountData Cubic.Counting.GeneralMonicData Filter Asymptotics

theorem cyclic_set (H : ℝ) : galoisSet .cyclic H = generalSet H := by
  ext f
  constructor
  · rintro ⟨⟨hf, hH⟩, hg⟩
    exact ⟨⟨hf, hg⟩, hH⟩
  · rintro ⟨⟨hf, hg⟩, hH⟩
    exact ⟨⟨hf, hH⟩, hg⟩

theorem estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox)
    (ε : ℝ) (hε : 0 < ε) :
    (fun H : ℝ => (N .cyclic H : ℝ) - H ^ 3 * P (Real.log H)) =O[atTop]
      (fun H : ℝ => H ^ (2 + ε)) := by
  have he : (fun H : ℝ => (N .cyclic H : ℝ) - H ^ 3 * P (Real.log H)) =
      (fun H : ℝ => (Nat.card (generalSet H) : ℝ) -
        (Cubic.Counting.GeneralMonicCount.Cmon * H ^ 3 * Real.log H +
          Cubic.Counting.GeneralMonicCount.Dmon * H ^ 3)) := by
    funext H
    rw [N, cyclic_set]
    dsimp [P]
    ring
  rw [he]
  exact Cubic.Counting.GeneralMonicCount.trace_count hPoisson hCN ε hε
end Cubic.AllGaloisCounts.CyclicCount
