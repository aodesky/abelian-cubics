import Cubic.BoxAsymptotic.PrimitiveLargeSieve
import Cubic.BoxAsymptotic.RayCoefficientBounds

/-! The ordinary angular large sieve after grouping lattice points on primitive
rays. The coefficient energy is retained explicitly: this permits summation
over disjoint norm intervals in the maximal-cutoff argument. -/

noncomputable section

namespace Cubic.BoxAsymptotic.GroupedLargeSieve

open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularSpacing
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.PrimitiveRays
open Cubic.BoxAsymptotic.RayCoefficientBounds Cubic.BoxAsymptotic.LatticeSums
open CubicTargets.BoxAsymptotic
open scoped BigOperators

def grouped (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (v : ℤ × ℤ) : ℂ :=
  ∑ p ∈ onRay S v, c p

theorem norm_grouped_le (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (v : ℤ × ℤ) :
    ‖grouped S c v‖ ≤ mass S c v := norm_sum_le _ _

theorem regroup {Y : ℝ} {S : Finset (ℤ × ℤ)} (hS : S ⊆ ball Y)
    (c : ℤ × ℤ → ℂ) (k : ℤ) :
    (∑ p ∈ S, c p * phase k (eis p)) =
      ∑ v ∈ rays Y, grouped S c v * phase k (eis v) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => maps_to_rays hS hp)
    (fun p => c p * phase k (eis p))]
  apply Finset.sum_congr rfl
  intro v hv
  rw [grouped, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpS, hpv⟩ := Finset.mem_filter.mp hp
  rw [phase_decompose k (mem_ball.mp (hS hpS)).1, hpv]

theorem finite_primitive_large_sieve
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    {N : ℕ} (hN : 0 < N) (M : ℤ) {Y : ℝ} (hY : 0 < Y)
    (c : ℤ × ℤ → ℂ) :
    (∑ n : Fin N, ‖∑ v ∈ rays Y,
      c v * phase (M + (n : ℤ) + 1) (eis v)‖ ^ 2) ≤
      ((N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3) *
        ∑ v ∈ rays Y, ‖c v‖ ^ 2 := by
  classical
  let e : Fin (rays Y).card ≃ ↥(rays Y) := (rays Y).equivFin.symm
  have hsum (f : ℤ × ℤ → ℂ) :
      (∑ i : Fin (rays Y).card, f (e i)) = ∑ v ∈ rays Y, f v := by
    exact (e.sum_comp (fun v : ↥(rays Y) => f v)).trans
      (Finset.sum_coe_sort (rays Y) f)
  have hsumR (f : ℤ × ℤ → ℝ) :
      (∑ i : Fin (rays Y).card, f (e i)) = ∑ v ∈ rays Y, f v := by
    exact (e.sum_comp (fun v : ↥(rays Y) => f v)).trans
      (Finset.sum_coe_sort (rays Y) f)
  have hi : Function.Injective (fun i : Fin (rays Y).card => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hp (i : Fin (rays Y).card) : prim (e i).val :=
    (Finset.mem_filter.mp (e i).property).2
  have hNY (i : Fin (rays Y).card) : (nrm (e i).val : ℝ) ≤ Y :=
    (mem_ball.mp (Finset.mem_filter.mp (e i).property).1).2
  have h := PrimitiveLargeSieve.primitive_large_sieve hLS hN M
    (fun i => (e i).val) hi hp hY hNY (fun i => c (e i).val)
  have hleft (k : ℤ) := hsum (fun v => c v * phase k (eis v))
  have hright := hsumR (fun v => ‖c v‖ ^ 2)
  simp only at hleft hright
  simpa only [hleft, hright] using h

theorem grouped_large_sieve
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    {N : ℕ} (hN : 0 < N) (M : ℤ) {Y : ℝ} (hY : 0 < Y)
    {S : Finset (ℤ × ℤ)} (hS : S ⊆ ball Y) (c : ℤ × ℤ → ℂ) :
    (∑ n : Fin N, ‖∑ p ∈ S,
      c p * phase (M + (n : ℤ) + 1) (eis p)‖ ^ 2) ≤
      ((N : ℝ) + 4 * Real.pi * Y / Real.sqrt 3) *
        ∑ v ∈ rays Y, mass S c v ^ 2 := by
  simp_rw [regroup hS c]
  apply (finite_primitive_large_sieve hLS hN M hY (grouped S c)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun v _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_grouped_le S c v) 2)

end Cubic.BoxAsymptotic.GroupedLargeSieve
