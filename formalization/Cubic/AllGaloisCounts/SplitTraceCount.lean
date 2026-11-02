import Cubic.AllGaloisCounts.SplitOrbits
import Cubic.AllGaloisCounts.TranslatedEllipseCount

/-! Sum the translated trace ellipses. The existing Riemann estimate for
`3+u²` gives the main term, with a uniform `O(H²)` total error. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SplitTraceCount
open CountData HeightBox SplitOrbits
open Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralHeightReduction
open Cubic.Counting.GeneralMonicCount (T card_T_le riemann_all)
open Cubic.Counting.GeneralMonicIntegrals
open Cubic.Counting.TraceZeroSplitCount (cubicOf)

def rootTrace (v : Fin 3 → ℤ) : ℤ := ∑ i, v i
def fiber (H : ℝ) (s : ℤ) : Set (Fin 3 → ℤ) := {v | v ∈ Triples H ∧ rootTrace v = s}
def center (s : ℤ) : ℝ × ℝ := ((s : ℝ) / 3, (s : ℝ) / 3)
def radiusSq (H : ℝ) (s : ℤ) : ℝ := H ^ 2 + (s : ℝ) ^ 2 / 3

theorem trace_mem {H : ℝ} {v : Fin 3 → ℤ} (hv : v ∈ Triples H) : rootTrace v ∈ T H := by
  have hH : 0 ≤ H := (height_nonneg _).trans hv
  have hh := ((HeightBox.height_iff hH).mp hv).1
  rw [cubicOf_eq] at hh
  simp only [splitCubic, monicCubic_coeff_two, Int.cast_neg, abs_neg] at hh
  have he : |(rootTrace v : ℝ)| ≤ H := by
    simpa only [rootTrace, Fin.sum_univ_three] using hh
  simpa only [T, Finset.mem_Icc, Set.mem_Icc] using (int_abs_iff _ _).mp he

theorem pair_bijOn {H : ℝ} {s : ℤ} (hs : |(s : ℝ)| ≤ H) :
    Set.BijOn (fun v : Fin 3 → ℤ => (v 0, v 1)) (fiber H s)
      (TranslatedEllipseCount.points (center s) (radiusSq H s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v ⟨hv, ht⟩
    have hv2 : v 2 = s - v 0 - v 1 := by
      simp only [rootTrace, Fin.sum_univ_three] at ht
      omega
    change weightedHeight (cubicOf v) ≤ H at hv
    rw [cubicOf_eq, hv2, split_height_ellipse] at hv
    exact hv.2
  · intro v hv w hw h
    have hv0 := hv.2
    have hw0 := hw.2
    simp only [rootTrace, Fin.sum_univ_three] at hv0 hw0
    simp only [Prod.mk.injEq] at h
    funext i
    fin_cases i <;> simp <;> omega
  · rintro ⟨x, y⟩ hp
    refine ⟨![x, y, s - x - y], ⟨?_, ?_⟩, rfl⟩
    · change weightedHeight (cubicOf _) ≤ H
      rw [cubicOf_eq]
      exact (split_height_ellipse x y s H).mpr ⟨hs, hp⟩
    · simp [rootTrace, Fin.sum_univ_three]

theorem fiber_card {H : ℝ} {s : ℤ} (hs : |(s : ℝ)| ≤ H) :
    Nat.card (fiber H s) = Nat.card (TranslatedEllipseCount.points (center s) (radiusSq H s)) :=
  Nat.card_congr (pair_bijOn hs).equiv

theorem triples_card (H : ℝ) : Nat.card (Triples H) =
    ∑ s ∈ T H, Nat.card (TranslatedEllipseCount.points (center s) (radiusSq H s)) := by
  classical
  have hfin := triples_finite H
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := rootTrace) (t := T H)
      (fun v hv => trace_mem ((Set.Finite.mem_toFinset hfin).mp hv))]
  have hfib : ∀ s ∈ T H,
      (hfin.toFinset.filter (fun v => rootTrace v = s)).card = Nat.card (fiber H s) := by
    intro s _
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [fiber]
  rw [Finset.sum_congr rfl hfib]
  exact Finset.sum_congr rfl (fun s hs => fiber_card
    (Cubic.Counting.GeneralTraceDecomposition.abs_le_of_mem hs))

def areaSum (H : ℝ) : ℝ := ∑ s ∈ T H, 2 * Real.pi / Real.sqrt 3 * radiusSq H s

theorem lattice_sum_bound : ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
    |(Nat.card (Triples H) : ℝ) - areaSum H| ≤ K * H ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := TranslatedEllipseCount.count_bound
  refine ⟨6 * K, fun H hH => ?_⟩
  have hH0 : 0 ≤ H := by linarith
  have heach : ∀ s ∈ T H,
      |(Nat.card (TranslatedEllipseCount.points (center s) (radiusSq H s)) : ℝ) -
        2 * Real.pi / Real.sqrt 3 * radiusSq H s| ≤ K * (2 * H) := by
    intro s hs
    have hsH := Cubic.Counting.GeneralTraceDecomposition.abs_le_of_mem hs
    have hs2 : (s : ℝ) ^ 2 ≤ H ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hsH 2
    have hX : 1 ≤ radiusSq H s := by dsimp [radiusSq]; nlinarith [sq_nonneg (s : ℝ)]
    refine (hK (center s) (radiusSq H s) hX).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * H)).mpr
    dsimp [radiusSq]
    nlinarith
  rw [triples_card, Nat.cast_sum, areaSum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ s ∈ T H,
        |(Nat.card (TranslatedEllipseCount.points (center s) (radiusSq H s)) : ℝ) -
          2 * Real.pi / Real.sqrt 3 * radiusSq H s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ T H, K * (2 * H) := Finset.sum_le_sum heach
    _ = ((T H).card : ℝ) * (K * (2 * H)) := by simp
    _ ≤ (3 * H) * (K * (2 * H)) :=
      mul_le_mul_of_nonneg_right (card_T_le hH) (by positivity)
    _ = (6 * K) * H ^ 2 := by ring

theorem area_sum_bound : ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
    |areaSum H - 6 * splitLeading * H ^ 3| ≤ K * H ^ 2 := by
  let A : ℝ := 2 * Real.pi / (3 * Real.sqrt 3)
  have hA : 0 ≤ A := by positivity
  refine ⟨26 * A, fun H hH => ?_⟩
  have hH0 : H ≠ 0 := by linarith
  have he : areaSum H = A * H ^ 2 * ∑ s ∈ T H, g₁ (s / H) := by
    rw [areaSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [radiusSq, g₁, A]
    field_simp
  have hm : 6 * splitLeading * H ^ 3 = A * H ^ 2 * (H * (20 / 3)) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    dsimp [splitLeading, A]
    field_simp
    nlinarith
  have hr := riemann_all continuous_g₁ (by norm_num) lip_g₁ bound_g₁ hH
  rw [integral_g₁] at hr
  norm_num at hr
  rw [he, hm, ← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hA (sq_nonneg H))]
  calc _ ≤ (A * H ^ 2) * 26 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (26 * A) * H ^ 2 := by ring

theorem triples_bound : ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
    |(Nat.card (Triples H) : ℝ) - 6 * splitLeading * H ^ 3| ≤ K * H ^ 2 := by
  obtain ⟨K₁, h₁⟩ := lattice_sum_bound
  obtain ⟨K₂, h₂⟩ := area_sum_bound
  refine ⟨K₁ + K₂, fun H hH => ?_⟩
  have h := abs_add_le ((Nat.card (Triples H) : ℝ) - areaSum H)
    (areaSum H - 6 * splitLeading * H ^ 3)
  have he : (Nat.card (Triples H) : ℝ) - areaSum H +
      (areaSum H - 6 * splitLeading * H ^ 3) =
      (Nat.card (Triples H) : ℝ) - 6 * splitLeading * H ^ 3 := by ring
  rw [he] at h
  linarith [h₁ H hH, h₂ H hH]

end Cubic.AllGaloisCounts.SplitTraceCount
