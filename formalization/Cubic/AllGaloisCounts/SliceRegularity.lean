import Cubic.AllGaloisCounts.SliceThresholds
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The implicit-function step for the two moving endpoints. The open
parameter interval contains `[-1,1]`, including neighborhoods of its endpoints. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceRegularity
open CountData LinearFactorSlice SliceThresholds Filter
open scoped Topology

theorem crossing_contDiffAt {y t : ℝ} (hy : y ∈ Set.Ioo (-2) 2)
    (ht : t ∈ Set.Icc 0 2) : ContDiffAt ℝ 2 (crossing t) y := by
  let x := crossing t y
  have hx : 0 < x := crossing_pos hy ht
  let f : ℝ × ℝ → ℝ := fun p => psi p.2 p.1
  let L := fderiv ℝ f (y, x)
  let d := -(x ^ 2)⁻¹ - 2 * x - y
  have hd : d ≠ 0 := by
    have h : d < 0 := by dsimp [d]; linarith [inverse_square_bound hx, hy.1]
    exact h.ne
  have hfc : ContDiffAt ℝ 2 f (y, x) := by
    exact ((contDiffAt_const.add (contDiffAt_snd.inv hx.ne')).sub
      (contDiffAt_snd.pow 2)).sub (contDiffAt_snd.mul contDiffAt_fst)
  have hfd : HasFDerivAt f L (y, x) :=
    (hfc.differentiableAt (by norm_num)).hasFDerivAt
  have he : L (0, 1) = d :=
    (hfd.comp_hasDerivAt x ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))).unique
      (psi_deriv hx y)
  have hlin : ∀ z : ℝ, (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) z = d * z := by
    intro z
    change L (0, z) = d * z
    calc L (0, z) = L (z • (0, 1)) := by congr 1; simp
      _ = z * L (0, 1) := by rw [map_smul]; rfl
      _ = d * z := by rw [he]; ring
  have hI : IsContDiffImplicitAt 2 f L (y, x) := by
    refine ⟨hfd, hfc, ⟨?_, ?_⟩, by norm_num⟩
    · intro a b hab
      simp only [hlin] at hab
      exact mul_left_cancel₀ hd hab
    · intro z
      refine ⟨z / d, ?_⟩
      rw [hlin]
      field_simp
  let q := hI.implicitFunction
  have hqc : ContDiffAt ℝ 2 q y := hI.contDiffAt_implicitFunction
  have hqx : q y = x := hI.eventually_implicitFunction_apply_eq.self_of_nhds rfl
  have hpos : ∀ᶠ z in 𝓝 y, 0 < q z :=
    hqc.continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa only [hqx] using hx))
  have heq : ∀ᶠ z in 𝓝 y, q z = crossing t z := by
    filter_upwards [hpos, isOpen_Ioo.mem_nhds hy, hI.apply_implicitFunction] with z hz hzy hze
    apply crossing_unique hzy ht hz
    change psi (q z) z = psi x y at hze
    exact hze.trans (crossing_spec hy ht).2
  exact hqc.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)

theorem crossing_contDiffOn {t : ℝ} (ht : t ∈ Set.Icc 0 2) :
    ContDiffOn ℝ 2 (crossing t) (Set.Icc (-1) 1) := by
  intro y hy
  exact (crossing_contDiffAt ⟨by linarith [hy.1], by linarith [hy.2]⟩ ht).contDiffWithinAt

end Cubic.AllGaloisCounts.SliceRegularity
