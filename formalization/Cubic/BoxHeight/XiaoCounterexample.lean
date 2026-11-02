import Cubic.BoxHeight.FieldCount
import Cubic.BoxHeight.CubicSubfield
import Cubic.BoxHeight.PrimeReciprocals
import Cubic.BoxHeight.WidmerFieldCount

/-!
# The box-height count grows faster than `X (log X)²`

The argument of the Remark in `box_height_research_note.tex`, with the fields of prime
conductor. For a prime `p ≡ 1 (mod 3)` let `K_p ⊂ ℚ(ζ_p)` be the cyclic cubic field
(`CubicSubfield`), with `|Δ_{K_p}| ≤ p²`. By [Widmer 2016, Theorem 1.1] (`WidmerBlackBox`, the
only assumed input), `#{α ∈ 𝒪_{K_p} : M(α) ≤ Y} ≥ (4/p) Y (log Y)² − c₁ Y^{2/3} (log⁺ Y^{1/3})²`.
The minimal polynomials of the `α ∉ ℤ` with `M(α) ≤ X/3` are monic cyclic cubics of box
height at most `X` (`FieldCount`), at least `(#{M(α) ≤ X/3} − 2(X/3)^{1/3} − 1)/3` of them,
and distinct primes give disjoint sets. Since `Σ_{p ≡ 1 (3)} 1/p = ∞` (`PrimeReciprocals`),
`N_{C₃}^{(3)}(X) / (X (log X)²)` exceeds any bound.
-/

noncomputable section

namespace Cubic.BoxHeight.XiaoCounterexample

open NumberField Polynomial Filter CubicTargets.BoxHeight
open Cubic.BoxHeight.FieldPolynomials Cubic.BoxHeight.FieldCount Cubic.BoxHeight.CubicSubfield

/-- Primes `p ≡ 1 (mod 3)`. -/
abbrev Pr := {p : ℕ // p.Prime ∧ p % 3 = 1}

instance (p : Pr) : Fact p.1.Prime := ⟨p.2.1⟩

/-- The polynomials from `K_p` with `M(α) ≤ Y`. -/
def P (p : Pr) (Y : ℝ) : Set ℤ[X] := polySet (K p.1) Y

theorem finrank_Kp (p : Pr) : Module.finrank ℚ (K p.1) = 3 := finrank_K p.2.2

theorem B_Kp (p : Pr) : 8 / (p.1 : ℝ) ≤ WidmerBlackBox.B (K p.1) := by
  haveI := isTotallyReal_K p.2.2
  obtain ⟨k, -, hk2, hk⟩ := discr_K p.2.2
  have hp : (1 : ℝ) < p.1 := by exact_mod_cast p.2.1.one_lt
  refine WidmerFieldCount.B_ge (finrank_Kp p) (by linarith) ?_
  rw [← Int.cast_abs, Int.abs_eq_natAbs, hk]
  push_cast
  exact pow_le_pow_right₀ hp.le hk2

/-- The lower bound for one field: with `X = Y^{1/3} ≥ 1`,
`3 #P_p(Y) ≥ (4/p) Y (log Y)² − c₁ X² (log⁺ X)² − 2X − 1`. -/
theorem card_P_ge (hW : WidmerBlackBox.BlackBox) (p : Pr) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ X : ℝ, 1 ≤ X →
      4 / (p.1 : ℝ) * X ^ 3 * Real.log (X ^ 3) ^ 2 - c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 -
        2 * X - 1 ≤ 3 * (Nat.card (P p (X ^ 3)) : ℝ) := by
  haveI := isTotallyReal_K p.2.2
  obtain ⟨c₁, hc₁, h⟩ := WidmerFieldCount.card_polySet_ge hW
  exact ⟨c₁, hc₁, h (K p.1) (finrank_Kp p) _ (by exact_mod_cast p.2.1.pos) (B_Kp p)⟩

theorem P_disjoint {p q : Pr} (hpq : p ≠ q) (Y Y' : ℝ) : Disjoint (P p Y) (P q Y') := by
  refine Set.disjoint_left.mpr fun f hp hq => hpq ?_
  obtain ⟨e⟩ := algEquiv_of_mem (finrank_Kp p) (finrank_Kp q) hp hq
  have hd := NumberField.discr_eq_discr_of_algEquiv (K p.1) e
  obtain ⟨k, hk1, -, hk⟩ := discr_K p.2.2
  obtain ⟨l, hl1, -, hl⟩ := discr_K q.2.2
  have h : p.1 ^ k = q.1 ^ l := by rw [← hk, ← hl, hd]
  have hdvd : p.1 ∣ q.1 ^ l := h ▸ dvd_pow_self p.1 (by omega)
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2.1 q.2.1).mp (p.2.1.dvd_of_dvd_pow hdvd))

theorem P_subset (p : Pr) (X : ℝ) : P p (X / 3) ⊆ boxSet X := by
  have := polySet_subset_box (finrank_Kp p) (X / 3)
  rwa [show 3 * (X / 3) = X by ring] at this

/-- `N_{C₃}^{(3)}(X) ≥ Σ_{p ∈ S} #P_p(X/3)`. -/
theorem sum_le_boxCount (S : Finset Pr) (X : ℝ) :
    ∑ p ∈ S, Nat.card (P p (X / 3)) ≤ boxCount X := by
  classical
  have hfin : ∀ p : Pr, (P p (X / 3)).Finite := fun p => polySet_finite _
  set T := S.biUnion fun p => (hfin p).toFinset
  have hT : T.card = ∑ p ∈ S, Nat.card (P p (X / 3)) := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (hfin p)]
    · intro p _ q _ hpq
      rw [Function.onFun, Set.Finite.disjoint_toFinset]
      exact P_disjoint hpq _ _
  rw [← hT, boxCount, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (boxSet_finite X)]
  refine Finset.card_le_card fun f hf => ?_
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp hf
  exact (boxSet_finite X).mem_toFinset.mpr (P_subset p X ((hfin p).mem_toFinset.mp hp))

/-- Finite sets of primes `p ≡ 1 (mod 3)` with `Σ 1/p` as large as desired. -/
theorem exists_primes (σ : ℝ) : ∃ S : Finset Pr, σ ≤ ∑ p ∈ S, 1 / (p.1 : ℝ) := by
  classical
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg PrimeReciprocals.f_nonneg).mp
    PrimeReciprocals.not_summable_f
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop σ))
  refine ⟨(Finset.range N).subtype fun n => n.Prime ∧ n % 3 = 1, ?_⟩
  refine (hN N le_rfl).trans (le_of_eq ?_)
  rw [Finset.sum_subtype_eq_sum_filter (f := fun n : ℕ => 1 / (n : ℝ)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff : (n : ZMod 3) = 1 ↔ n % 3 = 1 := by
    rw [show (1 : ZMod 3) = ((1 : ℕ) : ZMod 3) by simp, ZMod.natCast_eq_natCast_iff']
  simp only [PrimeReciprocals.f, hiff]

/-- For every `A`, eventually `N_{C₃}^{(3)}(X) ≥ A X (log X)²`. -/
theorem eventually_ge (hW : WidmerBlackBox.BlackBox) (A : ℝ) :
    ∀ᶠ X : ℝ in atTop, A * X * Real.log X ^ 2 ≤ boxCount X := by
  choose c hc hPc using card_P_ge hW
  obtain ⟨S, hS⟩ := exists_primes (9 * (|A| + 1))
  -- one constant for the finitely many fields in `S`
  set c₁ : ℝ := ∑ p ∈ S, c p + 1
  have hc₁ : 0 < c₁ := by
    have := Finset.sum_nonneg fun p (_ : p ∈ S) => (hc p).le
    simp only [c₁]; linarith
  have hP : ∀ p ∈ S, ∀ X : ℝ, 1 ≤ X →
      4 / (p.1 : ℝ) * X ^ 3 * Real.log (X ^ 3) ^ 2 - c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 -
        2 * X - 1 ≤ 3 * (Nat.card (P p (X ^ 3)) : ℝ) := by
    intro p hp X hX
    have hcp : c p ≤ c₁ := by
      have := Finset.single_le_sum (fun q (_ : q ∈ S) => (hc q).le) hp
      simp only [c₁]; linarith
    have hm : c p * X ^ 2 * max 1 (Real.log X) ^ 2 ≤ c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 := by
      gcongr
    linarith [hPc p X hX]
  set n : ℝ := (S.card : ℝ)
  set T₀ : ℝ := n * (c₁ + 3) + 3
  rw [Filter.eventually_atTop]
  refine ⟨T₀ ^ 3, fun X hX => ?_⟩
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hT3 : 3 ≤ T₀ := by simp only [T₀]; nlinarith
  have hX27 : 27 ≤ X := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hT3 3
    norm_num at this; linarith
  have hX0 : 0 < X := by linarith
  set t := X ^ (1 / 3 : ℝ) with ht
  have htX : t ^ 3 = X := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have htT : T₀ ≤ t := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ T₀ ^ 3) hX (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [show (T₀ ^ 3) ^ (1 / 3 : ℝ) = T₀ by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num] at h
  have ht3 : 3 ≤ t := le_trans hT3 htT
  -- `Y = X/3 = X_c³`
  set Y := X / 3
  set Xc := Y ^ (1 / 3 : ℝ) with hXc
  have hY0 : 0 < Y := by positivity
  have hXc3 : Xc ^ 3 = Y := by
    rw [hXc, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; norm_num
  have hXc1 : 1 ≤ Xc := Real.one_le_rpow (by simp only [Y]; linarith) (by norm_num)
  have hXct : Xc ≤ t := Real.rpow_le_rpow hY0.le (by simp only [Y]; linarith) (by norm_num)
  -- logarithms
  set L := Real.log X
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hL : 3 * Real.log 3 ≤ L := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  have hL1 : 1 ≤ L := by linarith
  have hlogY : Real.log Y = L - Real.log 3 := Real.log_div hX0.ne' (by norm_num)
  have hlogY2 : L ^ 2 / 4 ≤ Real.log Y ^ 2 := by
    rw [hlogY]; nlinarith
  have hlogXc : max 1 (Real.log Xc) ≤ L := by
    have hXcX : Xc ≤ X := by
      calc Xc ≤ t := hXct
        _ ≤ t ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        _ = X := htX
    exact max_le hL1 (Real.log_le_log (by linarith) hXcX)
  -- the per-field bounds, summed over `S`
  set E := c₁ * Xc ^ 2 * max 1 (Real.log Xc) ^ 2 - 0 + 2 * Xc + 1
  have hper : ∀ p ∈ S, 4 / (p.1 : ℝ) * Y * Real.log Y ^ 2 - E ≤ 3 * (Nat.card (P p Y) : ℝ) := by
    intro p hp
    have h := hP p hp Xc hXc1
    rw [hXc3] at h
    simp only [E]; linarith
  have hsum := Finset.sum_le_sum hper
  have e1 : ∑ p ∈ S, (4 / (p.1 : ℝ) * Y * Real.log Y ^ 2 - E) =
      4 * (∑ p ∈ S, 1 / (p.1 : ℝ)) * Y * Real.log Y ^ 2 - n * E := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : ∑ p ∈ S, 3 * (Nat.card (P p Y) : ℝ) = 3 * ∑ p ∈ S, (Nat.card (P p Y) : ℝ) := by
    rw [Finset.mul_sum]
  rw [e1, e2] at hsum
  have hbox : (∑ p ∈ S, (Nat.card (P p Y) : ℝ)) ≤ boxCount X := by
    exact_mod_cast sum_le_boxCount S X
  -- the main term
  have hmain : 3 * X * L ^ 2 * (|A| + 1) ≤ 4 * (∑ p ∈ S, 1 / (p.1 : ℝ)) * Y * Real.log Y ^ 2 := by
    have h1 : 0 ≤ 4 * Y := by positivity
    calc 3 * X * L ^ 2 * (|A| + 1) = 4 * (9 * (|A| + 1)) * Y * (L ^ 2 / 4) := by
          simp only [Y]; ring
      _ ≤ 4 * (∑ p ∈ S, 1 / (p.1 : ℝ)) * Y * Real.log Y ^ 2 := by
          gcongr
  -- the error
  have hE : n * E ≤ X * L ^ 2 := by
    have hXc2 : Xc ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) hXct 2
    have hm2 : max 1 (Real.log Xc) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hlogXc 2
    have hE1 : E ≤ (c₁ + 3) * t ^ 2 * L ^ 2 := by
      simp only [E]
      have a1 : c₁ * Xc ^ 2 * max 1 (Real.log Xc) ^ 2 ≤ c₁ * t ^ 2 * L ^ 2 := by
        gcongr
      have ht2L : t ^ 2 ≤ t ^ 2 * L ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      have tt : t ≤ t ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      have t1 : 1 ≤ t ^ 2 := one_le_pow₀ (by linarith)
      have a2 : 2 * Xc + 1 ≤ 3 * (t ^ 2 * L ^ 2) := by linarith
      have e : (c₁ + 3) * t ^ 2 * L ^ 2 = c₁ * t ^ 2 * L ^ 2 + 3 * (t ^ 2 * L ^ 2) := by ring
      linarith
    calc n * E ≤ n * ((c₁ + 3) * t ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_left hE1 hn
      _ = (n * (c₁ + 3)) * (t ^ 2 * L ^ 2) := by ring
      _ ≤ t * (t ^ 2 * L ^ 2) := by
          gcongr; linarith
      _ = X * L ^ 2 := by rw [← htX]; ring
  have hA : A * X * L ^ 2 ≤ |A| * X * L ^ 2 := by
    gcongr; exact le_abs_self A
  have hXL : 0 ≤ X * L ^ 2 := by positivity
  linarith

/-- `N_{C₃}^{(3)}(X) / (X (log X)²) → ∞`, assuming [Widmer 2016, Theorem 1.1]. -/
theorem unboundedRatio (hW : WidmerBlackBox.BlackBox) : UnboundedRatio := by
  refine ⟨boxSet_finite, Filter.tendsto_atTop.mpr fun A => ?_⟩
  filter_upwards [eventually_ge hW A, Filter.eventually_gt_atTop (Real.exp 1)] with X h hX
  have hX1 : 1 < X := lt_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hX
  have hL : 0 < Real.log X := Real.log_pos hX1
  rw [le_div_iff₀ (by positivity)]
  linarith [show A * (X * Real.log X ^ 2) = A * X * Real.log X ^ 2 by ring]

/-- The upper bound of [Xiao, Theorem 1.1] fails, assuming [Widmer 2016, Theorem 1.1]. -/
theorem not_xiaoUpperBound (hW : WidmerBlackBox.BlackBox) : ¬ XiaoUpperBound := by
  rintro ⟨k₁, k₂, -, -, h⟩
  obtain ⟨X, hk, hX⟩ := ((eventually_ge hW k₁).and (Filter.eventually_gt_atTop k₂)).exists
  exact absurd (h X hX) (not_lt.mpr hk)

end Cubic.BoxHeight.XiaoCounterexample
