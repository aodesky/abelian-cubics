import Cubic.BoxHeight.LowerBoundFields
import Cubic.BoxHeight.ConductorCount
import Cubic.BoxHeight.ConductorSum
import CubicTargets.BoxHeight.LowerBound
import Cubic.Counting.AsymptoticConstantIdentities

/-!
# Proof of `thm:lower`

Following `box_height_research_note.tex`. Put `Z = H^{1/3}` and take the fields `K_a` of
conductor `c_a ≤ Z` (`CyclicCubicFields`), with `|Δ_{K_a}| ≤ c_a²` (`CyclicCubicDiscriminant`),
so `B_{K_a} ≥ 8/c_a`. By [Widmer 2016, Theorem 1.1] with a constant independent of the field
(`WidmerFieldCount`), `3 P_{K_a}(H/3) ≥ (4/c_a)(H/3) log²(H/3) − E` with
`E = O(H^{2/3} log² H)`. Distinct fields give disjoint polynomial sets of box height at most `H`,
and each field is `K_a` for exactly two `a` (`LowerBoundFields`). The conductor sums
(`ConductorCount`, `ConductorSum`) give
`Σ_{c_a ≤ Z} 1/c_a ≥ (11/9) A₀ log Z − O(1)` and `#{a : c_a ≤ Z} = O(Z)`, where
`(11/9) A₀ = 2κ` in the note's notation. The main term is
`(2/9) H log²(H/3) · (11/27) A₀ log H = (11C/(27π√3)) H log H log²(H/3)`, and all errors are
`O(H log² H)`.

The only assumed input is `WidmerBlackBox.BlackBox`.
-/

noncomputable section

namespace Cubic.BoxHeight.LowerBound

open NumberField Polynomial CubicTargets.BoxHeight
open Cubic.BoxHeight.FieldCount Cubic.BoxHeight.CyclicCubicCharacters
open Cubic.BoxHeight.CyclicCubicFields Cubic.BoxHeight.LowerBoundFields

/-- The nonzero characters with conductor at most `Z`. -/
def Aset (P : SplitSet) (Z : ℝ) : Finset (ι P → ZMod 3) :=
  (Finset.univ.filter fun a => (CyclicCubicCharacters.cond P a : ℝ) ≤ Z).erase 0

theorem cond_zero (P : SplitSet) : CyclicCubicCharacters.cond P 0 = 1 := by
  simp [CyclicCubicCharacters.cond, supp]

theorem mem_Aset {P : SplitSet} {Z : ℝ} {a : ι P → ZMod 3} :
    a ∈ Aset P Z ↔ a ≠ 0 ∧ (CyclicCubicCharacters.cond P a : ℝ) ≤ Z := by
  simp [Aset]

/-- `Σ_{a ∈ A} f(c_a) = Σ_{c_a ≤ Z} f(c_a) − f(1)`. -/
theorem sum_Aset {P : SplitSet} {Z : ℝ} (hZ1 : 1 ≤ Z) (f : ℕ → ℝ) :
    ∑ a ∈ Aset P Z, f (CyclicCubicCharacters.cond P a) =
      (∑ a : ι P → ZMod 3, if (CyclicCubicCharacters.cond P a : ℝ) ≤ Z then f (CyclicCubicCharacters.cond P a) else 0) - f 1 := by
  have h0 : (0 : ι P → ZMod 3) ∈ Finset.univ.filter fun a => (CyclicCubicCharacters.cond P a : ℝ) ≤ Z := by
    simp [cond_zero, hZ1]
  rw [← Finset.sum_filter, ← Finset.sum_erase_add _ _ h0, cond_zero]
  simp [Aset]

/-- The conductor sums over the characters. -/
theorem conductor_bounds : ∃ B : ℝ, 0 ≤ B ∧ ∀ (P : SplitSet) (Z : ℝ),
    (∀ p : ℕ, p.Prime → p % 3 = 1 → (p : ℝ) ≤ Z → p ∈ P.S) → 9 ≤ Z →
      11 / 9 * ConductorSum.A₀ * Real.log Z - B ≤ ∑ a ∈ Aset P Z, (1 : ℝ) / CyclicCubicCharacters.cond P a ∧
        ((Aset P Z).card : ℝ) ≤ B * Z := by
  obtain ⟨B₁, hB₁⟩ := ConductorSum.log_lower
  obtain ⟨B₂, hB₂⟩ := ConductorSum.count_upper
  refine ⟨2 * |B₁| + |ConductorSum.A₀| * Real.log 9 + 1 + 2 * |B₂|, by positivity,
    fun P Z hZ hZ9 => ?_⟩
  have hZ0 : 0 ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZ91 : 1 ≤ Z / 9 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hg : ConductorCount.gc = ConductorSum.g := rfl
  constructor
  · have hs := ConductorCount.sum_cond hZ hZ0 le_rfl (fun m => 1 / (m : ℝ))
    have hs' := sum_Aset (P := P) hZ1 (fun m => 1 / (m : ℝ))
    rw [hs] at hs'
    simp only [Nat.cast_one, div_one] at hs'
    have e1 : ∑ m ∈ Finset.Icc 1 ⌊Z⌋₊, ConductorCount.gc m * (1 / (m : ℝ)) =
        ∑ m ∈ Finset.Icc 1 ⌊Z⌋₊, ConductorSum.g m / m := by
      rw [hg]; exact Finset.sum_congr rfl fun m _ => by ring
    have e2 : ∑ m ∈ Finset.Icc 1 ⌊Z / 9⌋₊, ConductorCount.gc m * (1 / ((9 * m : ℕ) : ℝ)) =
        1 / 9 * ∑ m ∈ Finset.Icc 1 ⌊Z / 9⌋₊, ConductorSum.g m / m := by
      rw [hg, Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by push_cast; ring
    have l1 := hB₁ Z hZ1
    have l2 := hB₁ (Z / 9) hZ91
    rw [Real.log_div (by linarith) (by norm_num), mul_sub] at l2
    have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    have a1 : ConductorSum.A₀ * Real.log 9 ≤ |ConductorSum.A₀| * Real.log 9 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog9
    have b1 := le_abs_self B₁
    have b2 := abs_nonneg B₂
    have b3 := abs_nonneg B₁
    have b4 : 0 ≤ |ConductorSum.A₀| * Real.log 9 := mul_nonneg (abs_nonneg _) hlog9
    rw [hs', e1, e2]
    linarith
  · have hs0 := ConductorCount.sum_cond hZ hZ0 le_rfl (fun _ => (1 : ℝ))
    have hs := sum_Aset (P := P) hZ1 (fun _ => (1 : ℝ))
    rw [hs0] at hs
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
    have c1 := hB₂ Z hZ1
    have c2 := hB₂ (Z / 9) hZ91
    rw [hg] at hs
    have b1 := le_abs_self B₂
    have hg0 : 0 ≤ ∑ m ∈ Finset.Icc 1 ⌊Z⌋₊, ConductorSum.g m :=
      Finset.sum_nonneg fun m _ => by unfold ConductorSum.g; split_ifs <;> positivity
    have hB₁0 := abs_nonneg B₁
    have hA0 : 0 ≤ |ConductorSum.A₀| * Real.log 9 :=
      mul_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))
    have hZB : |B₂| * (Z / 9) ≤ |B₂| * Z := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    nlinarith [mul_le_mul_of_nonneg_right b1 hZ0, mul_le_mul_of_nonneg_right b1 (by linarith : (0 : ℝ) ≤ Z / 9)]

/-- `11C/(27π√3) = (22/243) A₀`. -/
theorem constant_eq : 11 * Cubic.Counting.AsymptoticConstantsData.originalLeading /
    (27 * Real.pi * Real.sqrt 3) = 22 / 243 * ConductorSum.A₀ := by
  simp only [Cubic.Counting.AsymptoticConstantsData.originalLeading, ConductorSum.A₀]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-- The primes `p ≡ 1 (mod 3)` up to `Z`. -/
def splitSet (Z : ℝ) : SplitSet where
  S := (Finset.range (⌊Z⌋₊ + 1)).filter fun p => p.Prime ∧ p % 3 = 1
  prime _ hp := (Finset.mem_filter.mp hp).2.1
  mod_three _ hp := (Finset.mem_filter.mp hp).2.2

theorem mem_splitSet {Z : ℝ} :
    ∀ p : ℕ, p.Prime → p % 3 = 1 → (p : ℝ) ≤ Z → p ∈ (splitSet Z).S := by
  intro p hp h3 hpZ
  simp only [splitSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpZ), hp, h3⟩

theorem «thm:lower» (hW : WidmerBlackBox.BlackBox) : LowerClaim := by
  classical
  refine ⟨FieldCount.boxSet_finite, ?_⟩
  obtain ⟨B, hB0, hB⟩ := conductor_bounds
  obtain ⟨c₁, hc₁, hc⟩ := WidmerFieldCount.card_polySet_ge hW
  set K₀ := 11 * Cubic.Counting.AsymptoticConstantsData.originalLeading /
    (27 * Real.pi * Real.sqrt 3)
  have hK₀ : 0 ≤ K₀ := by
    have := Cubic.Counting.AsymptoticConstantIdentities.original_leading_positive
    positivity
  refine ⟨2 * Real.log 3 * K₀ + 2 / 9 * B + B * (c₁ + 3) / 6, 729, fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  -- `Z = H^{1/3}`, `X = (H/3)^{1/3}`, `Y = H/3 = X³`
  set Z := H ^ (1 / 3 : ℝ) with hZdef
  have hZ3 : Z ^ 3 = H := by
    rw [hZdef, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]; norm_num
  have hZ9 : 9 ≤ Z := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 729) hH (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [show (729 : ℝ) ^ (1 / 3 : ℝ) = 9 by
      rw [show (729 : ℝ) = 9 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num] at h
  set Y := H / 3
  set X := Y ^ (1 / 3 : ℝ) with hXdef
  have hY0 : 0 < Y := by positivity
  have hX3 : X ^ 3 = Y := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; norm_num
  have hX1 : 1 ≤ X := Real.one_le_rpow (by simp only [Y]; linarith) (by norm_num)
  have hXZ : X ≤ Z := Real.rpow_le_rpow hY0.le (by simp only [Y]; linarith) (by norm_num)
  -- logarithms
  set LH := Real.log H
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hLH3 : Real.log 3 ≤ LH := Real.log_le_log (by norm_num) (by linarith)
  have hLH1 : 1 ≤ LH := by linarith
  set LY := Real.log Y
  have hLY : LY = LH - Real.log 3 := Real.log_div hH0.ne' (by norm_num)
  have hLY0 : 0 ≤ LY := by rw [hLY]; linarith
  have hLYH : LY ≤ LH := by rw [hLY]; linarith
  have hLZ : Real.log Z = LH / 3 := by
    rw [hZdef, Real.log_rpow hH0]; ring
  have hlogX : max 1 (Real.log X) ≤ LH := by
    refine max_le hLH1 (Real.log_le_log (by linarith) ?_)
    calc X ≤ Z := hXZ
      _ ≤ Z ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      _ = H := hZ3
  -- the fields
  set P := splitSet Z
  obtain ⟨hsum, hcard⟩ := hB P Z mem_splitSet hZ9
  set A := Aset P Z
  have hA : ∀ a ∈ A, a ≠ 0 := fun a ha => (mem_Aset.mp ha).1
  have hneg : ∀ a ∈ A, -a ∈ A := fun a ha => by
    rw [mem_Aset] at ha ⊢
    exact ⟨neg_ne_zero.mpr ha.1, by rw [cond_neg]; exact ha.2⟩
  set E := c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 + 2 * X + 1
  have hper : ∀ a ∈ A, 4 / (CyclicCubicCharacters.cond P a : ℝ) * Y * LY ^ 2 - E ≤
      3 * (Nat.card (polySet (K P a) Y) : ℝ) := by
    intro a ha
    haveI := isTotallyReal_K (hA a ha)
    have hc0 : (0 : ℝ) < CyclicCubicCharacters.cond P a := by exact_mod_cast cond_pos P a
    have h := hc (K P a) (finrank_K (hA a ha)) (CyclicCubicCharacters.cond P a) hc0
      (WidmerFieldCount.B_ge (finrank_K (hA a ha)) hc0
        (CyclicCubicDiscriminant.abs_discr_le (hA a ha))) X hX1
    rw [hX3] at h
    simp only [E]; linarith
  -- `N_□(H) ≥ ½ Σ_a P_{K_a}(Y)`
  have hbox : (∑ a ∈ A, (Nat.card (polySet (K P a) Y) : ℝ)) ≤ 2 * boxCount H := by
    rw [sum_eq_two_mul A hA hneg fun F => (Nat.card (polySet F Y) : ℝ)]
    have := sum_le_boxCount A hA H
    have : (∑ F ∈ A.image (K P), (Nat.card (polySet F Y) : ℝ)) ≤ boxCount H := by
      exact_mod_cast this
    linarith
  have hsumper := Finset.sum_le_sum hper
  have e1 : ∑ a ∈ A, (4 / (CyclicCubicCharacters.cond P a : ℝ) * Y * LY ^ 2 - E) =
      4 * Y * LY ^ 2 * (∑ a ∈ A, (1 : ℝ) / CyclicCubicCharacters.cond P a) - A.card * E := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1, ← Finset.mul_sum] at hsumper
  -- the main term
  set S := ∑ a ∈ A, (1 : ℝ) / CyclicCubicCharacters.cond P a
  have hYL : 0 ≤ Y * LY ^ 2 := by positivity
  have hmain : 4 * Y * LY ^ 2 * (11 / 27 * ConductorSum.A₀ * LH - B) ≤ 4 * Y * LY ^ 2 * S := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hLZ] at hsum; linarith
  have hK : 4 * Y * LY ^ 2 * (11 / 27 * ConductorSum.A₀ * LH) = 6 * K₀ * H * LY ^ 2 * LH := by
    simp only [K₀, constant_eq, Y]; ring
  have hLY2 : LH ^ 2 - 2 * Real.log 3 * LH ≤ LY ^ 2 := by rw [hLY]; nlinarith
  have hmain2 : K₀ * H * (LH ^ 2 - 2 * Real.log 3 * LH) * LH ≤ K₀ * H * LY ^ 2 * LH :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLY2 (mul_nonneg hK₀ hH0.le))
      (by linarith)
  have hBY : 4 * Y * LY ^ 2 * B ≤ 4 / 3 * B * H * LH ^ 2 := by
    have : LY ^ 2 ≤ LH ^ 2 := pow_le_pow_left₀ hLY0 hLYH 2
    have h' : Y * LY ^ 2 ≤ Y * LH ^ 2 := mul_le_mul_of_nonneg_left this hY0.le
    calc 4 * Y * LY ^ 2 * B = 4 * B * (Y * LY ^ 2) := by ring
      _ ≤ 4 * B * (Y * LH ^ 2) := mul_le_mul_of_nonneg_left h' (by positivity)
      _ = 4 / 3 * B * H * LH ^ 2 := by simp only [Y]; ring
  -- the error
  have hE : E ≤ (c₁ + 3) * Z ^ 2 * LH ^ 2 := by
    have hX2 : X ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (by linarith) hXZ 2
    have hm2 : max 1 (Real.log X) ^ 2 ≤ LH ^ 2 :=
      pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hlogX 2
    have a1 : c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 ≤ c₁ * Z ^ 2 * LH ^ 2 := by gcongr
    have hZ2 : Z ≤ Z ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have hZ21 : 1 ≤ Z ^ 2 := one_le_pow₀ (by linarith)
    have hL2 : Z ^ 2 ≤ Z ^ 2 * LH ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLH1)
    simp only [E]; linarith only [a1, hXZ, hZ2, hZ21, hL2]
  have hE0 : 0 ≤ E := by simp only [E]; positivity
  have hcardE : (A.card : ℝ) * E ≤ B * (c₁ + 3) * H * LH ^ 2 := by
    calc (A.card : ℝ) * E ≤ (B * Z) * ((c₁ + 3) * Z ^ 2 * LH ^ 2) :=
          mul_le_mul hcard hE hE0 (by positivity)
      _ = B * (c₁ + 3) * Z ^ 3 * LH ^ 2 := by ring
      _ = B * (c₁ + 3) * H * LH ^ 2 := by rw [hZ3]
  -- assemble: `6 N_□(H) ≥ 3 Σ P ≥ 4 Y LY² S − #A E`
  have r1 : 4 * Y * LY ^ 2 * (11 / 27 * ConductorSum.A₀ * LH - B) =
      4 * Y * LY ^ 2 * (11 / 27 * ConductorSum.A₀ * LH) - 4 * Y * LY ^ 2 * B := by ring
  have r2 : K₀ * H * (LH ^ 2 - 2 * Real.log 3 * LH) * LH =
      K₀ * H * LH ^ 3 - 2 * Real.log 3 * K₀ * (H * LH ^ 2) := by ring
  have r3 : 6 * (K₀ * H * LY ^ 2 * LH) = 6 * K₀ * H * LY ^ 2 * LH := by ring
  have r4 : (2 * Real.log 3 * K₀ + 2 / 9 * B + B * (c₁ + 3) / 6) * H * LH ^ 2 =
      2 * Real.log 3 * K₀ * (H * LH ^ 2) + 2 / 9 * (B * H * LH ^ 2) +
        (B * (c₁ + 3) * H * LH ^ 2) / 6 := by ring
  have r5 : 4 / 3 * B * H * LH ^ 2 = 4 / 3 * (B * H * LH ^ 2) := by ring
  have r6 : K₀ * H * Real.log H ^ 3 = K₀ * H * LH ^ 3 := rfl
  rw [r1] at hmain
  rw [r2] at hmain2
  rw [r5] at hBY
  have t1 : 4 * Y * LY ^ 2 * S - (A.card : ℝ) * E ≤ 6 * (boxCount H : ℝ) := by
    linarith only [hsumper, hbox]
  have t2 : 6 * K₀ * H * LY ^ 2 * LH - 4 * Y * LY ^ 2 * B ≤ 4 * Y * LY ^ 2 * S := by
    rw [← hK]; exact hmain
  rw [r4]
  set u := K₀ * H * LY ^ 2 * LH
  set v := B * H * LH ^ 2
  set w := B * (c₁ + 3) * H * LH ^ 2
  set y := 4 * Y * LY ^ 2 * B
  set z := 4 * Y * LY ^ 2 * S
  set k := (A.card : ℝ) * E
  have t2' : 6 * u - y ≤ z := by linarith only [t2, r3]
  linarith only [t1, t2', hmain2, hBY, hcardE]

end Cubic.BoxHeight.LowerBound
