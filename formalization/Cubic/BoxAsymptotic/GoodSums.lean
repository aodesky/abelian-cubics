import Cubic.BoxAsymptotic.GoodSet

/-!
# The smoothing error summed over good pieces

The error of `SmoothSectorCounting` on a piece is `(6H/(XΘ)) Cst √X log(2X + 1/Θ)^A`.
On a good piece, `2^{2j} ≤ ε² X √X/(2000H)` (from `2000H ≤ ε²Θ²X√X`), so `Σ_j 2^j`
is at most twice the largest term, and a scale `i` carries good pieces only if
`√X ≤ ε² H/128000` (combine with `XΘ ≤ H/8`). Hence

  `Σ_{good} H/(XΘ) √X ≪ H Σ_i X^{-1/2} ε X^{3/4}/√H ≪ ε √H Σ_i X^{1/4} ≪ ε² H`,

and the total smoothing error is `≤ |Cst| (3 log H)^{max A 0} ε² H`: the draft's
`O(H L^{A-b-B/4})`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.GoodSums

open Cubic.BoxAsymptotic.GoodSet
open Cubic.BoxAsymptotic.BulkW (Good)
open scoped Classical

/-- A sum of `qⁱ` over indices with `qⁱ ≤ B` is at most `B q/(q - 1)`. -/
theorem geom_bounded {q B : ℝ} (hq : 1 < q) (hB : 0 ≤ B) (S : Finset ℕ)
    (hS : ∀ i ∈ S, q ^ i ≤ B) : ∑ i ∈ S, q ^ i ≤ B * q / (q - 1) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; have : 0 < q - 1 := by linarith
    positivity
  set J := S.max' hne
  have hsub : S ⊆ Finset.range (J + 1) := fun i hi =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' i hi))
  have hq0 : 0 < q - 1 := by linarith
  calc ∑ i ∈ S, q ^ i ≤ ∑ i ∈ Finset.range (J + 1), q ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (q ^ (J + 1) - 1) / (q - 1) := geom_sum_eq (ne_of_gt hq) _
    _ ≤ q ^ (J + 1) / (q - 1) := by
        apply div_le_div_of_nonneg_right _ hq0.le; linarith
    _ = q ^ J * q / (q - 1) := by rw [pow_succ]
    _ ≤ B * q / (q - 1) := by
        apply div_le_div_of_nonneg_right _ hq0.le
        exact mul_le_mul_of_nonneg_right (hS J (S.max'_mem hne)) (by linarith)

theorem sqrt_sqrt_pow (i : ℕ) :
    Real.sqrt (Real.sqrt ((2 : ℝ) ^ i)) = Real.sqrt (Real.sqrt 2) ^ i := by
  rw [Cubic.BoxAsymptotic.Bands.sqrt_pow' (by norm_num),
    Cubic.BoxAsymptotic.Bands.sqrt_pow' (Real.sqrt_nonneg _)]

/-- The piece scales. -/
def X (p : ℕ × ℕ) : ℝ := 2 ^ p.1

def Θ (p : ℕ × ℕ) : ℝ := (1 / 2) ^ p.2

/-- **The key sum**: `Σ_{good} (H/(XΘ)) √X ≤ ε² H/500`. -/
theorem sum_good {H ε : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∑ p ∈ G H ε, H / (X p * Θ p) * Real.sqrt (X p) ≤ ε ^ 2 * H / 500 := by
  have hH0 : 0 < H := by linarith
  set q := Real.sqrt (Real.sqrt 2)
  have hq := Cubic.BoxAsymptotic.Bands.q_gt
  -- group by `i`
  set Is := (G H ε).image Prod.fst
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Is)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  -- inner sums
  have hinner : ∀ i ∈ Is, ∑ p ∈ (G H ε).filter (fun p => p.1 = i),
      H / (X p * Θ p) * Real.sqrt (X p) ≤
        H * (2 * ε / Real.sqrt (2000 * H)) * q ^ i := by
    intro i _
    set Xi : ℝ := 2 ^ i
    have hXi : 0 < Xi := by positivity
    set B := ε * Real.sqrt (Xi * Real.sqrt Xi) / Real.sqrt (2000 * H)
    have hB0 : 0 ≤ B := by positivity
    -- each good `j` has `2^j ≤ B`
    have hj : ∀ p ∈ (G H ε).filter (fun p => p.1 = i), (2 : ℝ) ^ p.2 ≤ B := by
      intro p hp
      obtain ⟨hpG, rfl⟩ := Finset.mem_filter.mp hp
      have hg := mem_G hpG
      have h2 : 2000 * H ≤ ε ^ 2 * ((1 / 2 : ℝ) ^ p.2) ^ 2 * (Xi * Real.sqrt Xi) := hg.g2
      have e : (2 : ℝ) ^ p.2 * (1 / 2) ^ p.2 = 1 := by rw [← mul_pow]; norm_num
      have hsq : ((2 : ℝ) ^ p.2) ^ 2 * (2000 * H) ≤ ε ^ 2 * (Xi * Real.sqrt Xi) := by
        have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ((2 : ℝ) ^ p.2))
        calc ((2 : ℝ) ^ p.2) ^ 2 * (2000 * H) ≤ ((2 : ℝ) ^ p.2) ^ 2 *
              (ε ^ 2 * ((1 / 2 : ℝ) ^ p.2) ^ 2 * (Xi * Real.sqrt Xi)) := this
          _ = (2 ^ p.2 * (1 / 2) ^ p.2) ^ 2 * (ε ^ 2 * (Xi * Real.sqrt Xi)) := by ring
          _ = _ := by rw [e]; ring
      rw [le_div_iff₀ (by positivity)]
      have h' := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hε0.le] at h'
      exact h'
    have hsum : ∑ p ∈ (G H ε).filter (fun p => p.1 = i), (2 : ℝ) ^ p.2 ≤ 2 * B := by
      have := geom_bounded (q := 2) (by norm_num) hB0
        (((G H ε).filter (fun p => p.1 = i)).image Prod.snd) (fun j hj' => by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj'
          exact hj p hp)
      rw [Finset.sum_image (fun p hp p' hp' h => Prod.ext ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hp').2.symm) h)] at this
      linarith [show B * 2 / (2 - 1) = 2 * B by ring]
    have hterm : ∀ p ∈ (G H ε).filter (fun p => p.1 = i),
        H / (X p * Θ p) * Real.sqrt (X p) = H * Real.sqrt Xi / Xi * (2 : ℝ) ^ p.2 := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hX : X p = Xi := by simp only [X, hp', Xi]
      rw [hX]
      simp only [Θ]
      rw [one_div_pow]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have e1 : Real.sqrt (Xi * Real.sqrt Xi) = Real.sqrt Xi * Real.sqrt (Real.sqrt Xi) :=
      Real.sqrt_mul hXi.le _
    have e2 : Real.sqrt Xi * Real.sqrt Xi = Xi := Real.mul_self_sqrt hXi.le
    have hqi : q ^ i = Real.sqrt (Real.sqrt Xi) := (sqrt_sqrt_pow i).symm
    calc H * Real.sqrt Xi / Xi * ∑ p ∈ (G H ε).filter (fun p => p.1 = i), (2 : ℝ) ^ p.2
        ≤ H * Real.sqrt Xi / Xi * (2 * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = H * (2 * ε / Real.sqrt (2000 * H)) *
            ((Real.sqrt Xi * Real.sqrt Xi) / Xi * Real.sqrt (Real.sqrt Xi)) := by
          simp only [B]; rw [e1]; ring
      _ = H * (2 * ε / Real.sqrt (2000 * H)) * q ^ i := by
          rw [e2, div_self hXi.ne', one_mul, hqi]
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [← Finset.mul_sum]
  -- the scales with a good piece have `q^i ≤ ε √H/357`
  have hi : ∀ i ∈ Is, q ^ i ≤ ε * Real.sqrt H / 357 := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    have hg := mem_G hp
    set Xi : ℝ := 2 ^ p.1
    set Θi : ℝ := (1 / 2) ^ p.2
    have hXi : 0 < Xi := by positivity
    have hΘi : 0 < Θi := by positivity
    have h2 : 2000 * H ≤ ε ^ 2 * Θi ^ 2 * (Xi * Real.sqrt Xi) := hg.g2
    have h3 : Xi * Θi ≤ H / 8 := hg.g3
    have hsX : 0 < Real.sqrt Xi := Real.sqrt_pos.mpr hXi
    -- `√X ≤ ε² H/128000`
    have hs : Real.sqrt Xi ≤ ε ^ 2 * H / 128000 := by
      have hΘ2 : (Xi * Θi) ^ 2 ≤ (H / 8) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      have e2 : Real.sqrt Xi * Real.sqrt Xi = Xi := Real.mul_self_sqrt hXi.le
      -- `2000 H X² ≤ ε² (XΘ)² X √X ≤ ε² H²/64 · X √X`
      have : 2000 * H * Xi ^ 2 ≤ ε ^ 2 * (H / 8) ^ 2 * (Xi * Real.sqrt Xi) := by
        have := mul_le_mul_of_nonneg_left h2 (sq_nonneg Xi)
        calc 2000 * H * Xi ^ 2 = Xi ^ 2 * (2000 * H) := by ring
          _ ≤ Xi ^ 2 * (ε ^ 2 * Θi ^ 2 * (Xi * Real.sqrt Xi)) := this
          _ = ε ^ 2 * (Xi * Θi) ^ 2 * (Xi * Real.sqrt Xi) := by ring
          _ ≤ ε ^ 2 * (H / 8) ^ 2 * (Xi * Real.sqrt Xi) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘ2 (by positivity))
              (by positivity)
      set t := Real.sqrt Xi
      have hX2 : Xi = t ^ 2 := by rw [sq]; exact e2.symm
      rw [hX2] at this
      have ht3 : 0 < t ^ 3 := by positivity
      have h5 : (2000 * H * t) * t ^ 3 ≤ (ε ^ 2 * (H / 8) ^ 2) * t ^ 3 := by
        have e3 : (2000 * H * t) * t ^ 3 = 2000 * H * (t ^ 2) ^ 2 := by ring
        have e4 : (ε ^ 2 * (H / 8) ^ 2) * t ^ 3 = ε ^ 2 * (H / 8) ^ 2 * (t ^ 2 * t) := by ring
        rw [e3, e4]; exact this
      have h6 := le_of_mul_le_mul_right h5 ht3
      rw [le_div_iff₀ (by norm_num)]
      have e5 : ε ^ 2 * (H / 8) ^ 2 = ε ^ 2 * H * H / 64 := by ring
      rw [e5] at h6
      have : t * (2000 * H) ≤ t * 0 + ε ^ 2 * H * H / 64 := by linarith
      nlinarith
    rw [← sqrt_sqrt_pow]
    have : Real.sqrt (Real.sqrt Xi) ≤ Real.sqrt (ε ^ 2 * H / 128000) := Real.sqrt_le_sqrt hs
    refine this.trans ?_
    · rw [show ε ^ 2 * H / 128000 = ε ^ 2 * (H / 128000) by ring, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hε0.le, Real.sqrt_div' _ (by norm_num)]
      have : (357 : ℝ) ≤ Real.sqrt 128000 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hε0.le
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) this
  have hgeo := geom_bounded (by linarith : 1 < q) (by positivity) Is hi
  have hq7 : q / (q - 1) ≤ 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hsH : Real.sqrt (2000 * H) = Real.sqrt 2000 * Real.sqrt H := Real.sqrt_mul (by norm_num) _
  have h2000 : (44 : ℝ) ≤ Real.sqrt 2000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsHpos : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH0
  have hsHH : Real.sqrt H * Real.sqrt H = H := Real.mul_self_sqrt hH0.le
  calc H * (2 * ε / Real.sqrt (2000 * H)) * ∑ i ∈ Is, q ^ i
      ≤ H * (2 * ε / Real.sqrt (2000 * H)) * (ε * Real.sqrt H / 357 * q / (q - 1)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = H * (2 * ε / (Real.sqrt 2000 * Real.sqrt H)) * (ε * Real.sqrt H / 357) *
          (q / (q - 1)) := by rw [hsH]; ring
    _ ≤ H * (2 * ε / (Real.sqrt 2000 * Real.sqrt H)) * (ε * Real.sqrt H / 357) * 7 :=
        mul_le_mul_of_nonneg_left hq7 (by positivity)
    _ = 14 * ε ^ 2 * H / (357 * Real.sqrt 2000) := by field_simp; ring
    _ ≤ ε ^ 2 * H / 500 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : 0 ≤ ε ^ 2 * H := by positivity
        nlinarith

end Cubic.BoxAsymptotic.GoodSums
