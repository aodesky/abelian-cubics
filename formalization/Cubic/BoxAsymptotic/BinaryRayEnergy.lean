import Cubic.BoxAsymptotic.GroupedLargeSieve
import CubicTargets.BoxAsymptotic.BinaryDecomposition

/-! Norm intervals and the energy estimate at one level of the binary
decomposition. Disjoint intervals share one total ray energy; estimating each
interval separately by the full norm-ball bound would lose this fact. -/

noncomputable section

namespace Cubic.BoxAsymptotic.BinaryRayEnergy

open Cubic.BoxAsymptotic.PrimitiveRays Cubic.BoxAsymptotic.RayCoefficientBounds
open Cubic.BoxAsymptotic.EisensteinCoordinates
open CubicTargets.BoxAsymptotic.BinaryDecomposition

def normIndex (p : ℤ × ℤ) : ℕ := (nrm p).toNat

def restrict (S : Finset (ℤ × ℤ)) (E : Finset ℕ) : Finset (ℤ × ℤ) :=
  S.filter (fun p => normIndex p ∈ E)

def byNorm (S : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ S.filter (fun p => normIndex p = n), f p

theorem sum_byNorm (S : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℂ) (E : Finset ℕ) :
    (∑ n ∈ E, byNorm S f n) = ∑ p ∈ restrict S E, f p :=
  Finset.sum_fiberwise_eq_sum_filter S E normIndex f

theorem blocks_disjoint (j : ℕ) :
    Pairwise (fun b c : ℕ => Disjoint (block j b) (block j c)) := by
  intro b c hbc
  rcases lt_or_gt_of_ne hbc with h | h
  · exact Finset.Ioc_disjoint_Ioc_of_le
      (Nat.mul_le_mul_left (2 ^ j) (Nat.succ_le_of_lt h))
  · exact (Finset.Ioc_disjoint_Ioc_of_le
      (Nat.mul_le_mul_left (2 ^ j) (Nat.succ_le_of_lt h))).symm

theorem restrict_disjoint (S : Finset (ℤ × ℤ)) {E F : Finset ℕ}
    (h : Disjoint E F) : Disjoint (restrict S E) (restrict S F) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hp).2
    (Finset.mem_filter.mp hq).2

theorem onRay_restrict (S : Finset (ℤ × ℤ)) (E : Finset ℕ) (v : ℤ × ℤ) :
    onRay (restrict S E) v = restrict (onRay S v) E := by
  simp only [onRay, restrict, Finset.filter_filter]
  congr 1
  funext p
  exact propext and_comm

theorem mass_disjoint (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (v : ℤ × ℤ) (B : Finset ℕ) (E : ℕ → Finset ℕ)
    (hE : Set.PairwiseDisjoint (↑B) E) :
    (∑ b ∈ B, mass (restrict S (E b)) c v ^ 2) ≤ mass S c v ^ 2 := by
  classical
  have hd : Set.PairwiseDisjoint (↑B) (fun b => restrict (onRay S v) (E b)) := by
    intro b hb d hd hbd
    exact restrict_disjoint _ (hE hb hd hbd)
  have hs : (B.biUnion (fun b => restrict (onRay S v) (E b))) ⊆ onRay S v := by
    intro p hp
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hb).1
  have hmass : (∑ b ∈ B, mass (restrict S (E b)) c v) ≤ mass S c v := by
    simp only [mass, onRay_restrict]
    rw [← Finset.sum_biUnion hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => norm_nonneg (c p))
  calc
    (∑ b ∈ B, mass (restrict S (E b)) c v ^ 2) ≤
        (∑ b ∈ B, mass (restrict S (E b)) c v) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun b _ => mass_nonneg _ c v)
    _ ≤ mass S c v ^ 2 := pow_le_pow_left₀
      (Finset.sum_nonneg (fun b _ => mass_nonneg _ c v)) hmass 2

theorem level_energy (Y : ℝ) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (j J : ℕ) :
    (∑ b ∈ Finset.range (2 ^ J), ∑ v ∈ rays Y,
      mass (restrict S (block j b)) c v ^ 2) ≤ ∑ v ∈ rays Y, mass S c v ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun v _ => mass_disjoint S c v _ _
    (fun _ _ _ _ h => blocks_disjoint j h))

end Cubic.BoxAsymptotic.BinaryRayEnergy
