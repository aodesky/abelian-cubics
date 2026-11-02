import Cubic.BoxAsymptotic.MainTerm
import Cubic.BoxAsymptotic.Reduction
import Cubic.BoxAsymptotic.MainConsequences
import Cubic.BoxAsymptotic.SmoothSector
import Cubic.BoxAsymptotic.SmoothProductCounting

/-!
# `thm:main`, from the cited analytic inputs

`N_□(H) = A₃ H (log H)³ + O(H (log H)² log log H)`.
The geometric reduction `of_smoothing` assumes `SmoothSectorCounting`;
the final `thm:main` supplies it from the full proved smoothing lemma.

With `L = log H` and `ε = L^{-b}`, `b = max(A, 0)/2 + 1` (`A` the exponent of the smoothing
hypothesis for our profiles):

* `N_□ = (1/6) Σ_β W + O(H L²)` (`Reduction.reduction`, `eq:continuous`);
* `(1/6) Σ_β W (1 - w_bulk) = O(H L² (1 + log(1/ε))) = O(H L² log L)`
  (`Discard.discard`, `Core`);
* `(1/6) Σ_β W w_bulk = 2 Σ_{good} M(i) + O(ε Σ |M| + ε² L^{A'} H) = 2 Σ M + O(H L²)`
  (`BulkSum.bulk`);
* `2 Σ M = A₃ H L³ + O(H L² (1 + log(1/ε)))` (`MainTerm.main_eval`).
-/

noncomputable section

namespace Cubic.BoxAsymptotic.MainTheorem

open Real
open CubicTargets.BoxAsymptotic (aStar A3 SmoothSectorCounting MainClaim)
open Cubic.BoxAsymptotic.Admissible (Bset θ mem_Bset)
open Cubic.BoxAsymptotic.TraceWidth (W W_nonneg)
open Cubic.BoxAsymptotic.BulkSum (wb M)
open Cubic.BoxAsymptotic.GoodSet (G)
open Cubic.BoxAsymptotic.PartitionIntegrals (c₁)
open Cubic.BoxAsymptotic.GoodCount (D)

/-- Logarithmic facts for `H ≥ e^{10}`. -/
theorem log_facts {H : ℝ} (hH : Real.exp 10 ≤ H) :
    3 ≤ H ∧ 10 ≤ Real.log H ∧ 1 ≤ Real.log (Real.log H) := by
  have hH0 : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hH
  have hL : 10 ≤ Real.log H := by rw [Real.le_log_iff_exp_le hH0]; exact hH
  refine ⟨?_, hL, ?_⟩
  · have : (3 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ); linarith
    linarith
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith

theorem logb_le_two_log {x : ℝ} (hx : 1 ≤ x) : logb 2 x ≤ 2 * Real.log x := by
  have hl2 := Real.log_two_gt_d9
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [logb, div_le_iff₀ (by positivity)]; nlinarith


/-- The choice `ε = L^{-b}`. -/
theorem eps_facts {L A' : ℝ} (hL : 10 ≤ L) (hA' : 0 ≤ A') :
    0 < (L ^ (A' / 2 + 1))⁻¹ ∧ (L ^ (A' / 2 + 1))⁻¹ ≤ 1 / L ∧
      logb 2 (1 / (L ^ (A' / 2 + 1))⁻¹) = (A' / 2 + 1) * logb 2 L ∧
      L ^ A' * ((L ^ (A' / 2 + 1))⁻¹) ^ 2 ≤ 1 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hpos : 0 < L ^ (A' / 2 + 1) := Real.rpow_pos_of_pos hL0 _
  have hge : L ≤ L ^ (A' / 2 + 1) := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ (A' / 2 + 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  refine ⟨inv_pos.mpr hpos, ?_, ?_, ?_⟩
  · rw [one_div]; exact inv_anti₀ hL0 hge
  · rw [one_div, inv_inv, Real.logb_rpow_eq_mul_logb_of_pos hL0]
  · have e : (L ^ (A' / 2 + 1)) ^ 2 = L ^ A' * L ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      congr 1; push_cast; ring
    rw [inv_pow, e, mul_inv, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hL0 _).ne',
      one_mul]
    have : 1 ≤ L ^ (2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    exact inv_le_one_of_one_le₀ this

/-- Pure arithmetic of the final combination. -/
theorem combine {N T Tb S2 Main B1 B2 B3 B4 B5 : ℝ} (h1 : |N - T| ≤ B1)
    (h2a : 0 ≤ T - Tb) (h2b : T - Tb ≤ B2) (h3 : |Tb - S2| ≤ B3 + B4) (h5 : |S2 - Main| ≤ B5) :
    |N - Main| ≤ B1 + B2 + B3 + B4 + B5 := by
  rw [abs_le] at h1 h3 h5 ⊢
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2, h5.1, h5.2]

theorem le_LL {x H L LL : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) (hLL : 1 ≤ LL) :
    x * (H * L ^ 2) ≤ x * (H * L ^ 2 * LL) :=
  mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hLL) hx

theorem disc_arith {Kd H L LL b l : ℝ} (hKd : 0 ≤ Kd) (hH : 0 ≤ H) (hb : 1 ≤ b) (hLL : 1 ≤ LL)
    (hl : l ≤ 2 * LL) :
    1 / 6 * (Kd * H * L ^ 2 * (1 + b * l)) ≤ Kd * (1 + 4 * b) / 6 * (H * L ^ 2 * LL) := by
  have h1 : 1 + b * l ≤ (1 + 4 * b) * LL := by
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ b)
    nlinarith
  have h2 : 0 ≤ Kd * H * L ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h1 h2
  calc 1 / 6 * (Kd * H * L ^ 2 * (1 + b * l)) ≤ 1 / 6 * (Kd * H * L ^ 2 * ((1 + 4 * b) * LL)) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ = _ := by ring

theorem e1_arith {ε L CM H S LL : ℝ} (hL : 1 ≤ L) (hεL : ε ≤ 1 / L) (hCM : 0 ≤ CM)
    (hH : 0 ≤ H) (hS0 : 0 ≤ S) (hS : S ≤ CM * (H * L ^ 3)) (hLL : 1 ≤ LL) :
    28 * ε * S ≤ 28 * CM * (H * L ^ 2 * LL) := by
  have hL0 : 0 < L := by linarith
  have a1 : ε * S ≤ 1 / L * (CM * (H * L ^ 3)) := mul_le_mul hεL hS hS0 (by positivity)
  have e2 : 1 / L * (CM * (H * L ^ 3)) = CM * (H * L ^ 2) := by field_simp
  have a2 := le_LL (L := L) hCM hH hLL
  nlinarith

theorem sM_arith {c H a l2 L k : ℝ} (hc : 0 ≤ c) (hH : 0 ≤ H) (hk : 0 ≤ k) (hL : 1 ≤ L) :
    c * H * (a * l2 * (4 * L) + k) * (30 * L ^ 2) ≤ c * (4 * a * l2 + k) * 30 * (H * L ^ 3) := by
  have : a * l2 * (4 * L) + k ≤ (4 * a * l2 + k) * L := by
    have : k ≤ k * L := le_mul_of_one_le_right hk hL
    nlinarith
  have h0 : 0 ≤ c * H := by positivity
  have := mul_le_mul_of_nonneg_left this h0
  have h30 : 0 ≤ 30 * L ^ 2 := by positivity
  calc c * H * (a * l2 * (4 * L) + k) * (30 * L ^ 2) ≤ c * H * ((4 * a * l2 + k) * L) * (30 * L ^ 2) :=
        mul_le_mul_of_nonneg_right this h30
    _ = _ := by ring

theorem hm1_arith {Dv b LL h L : ℝ} (hD : Dv ≤ (4 * b + 10) * LL) (hD0 : 0 ≤ Dv)
    (hLL : 1 ≤ LL) (hh : h ≤ 2 * L) (hh0 : 0 ≤ h) (hL : 2 ≤ L) :
    Dv * (2 * h + 2) ^ 2 + 16 * h ^ 2 ≤ (25 * (4 * b + 10) + 64) * (L ^ 2 * LL) := by
  have hq : (2 * h + 2) ^ 2 ≤ 25 * L ^ 2 := by nlinarith
  have t1 : Dv * (2 * h + 2) ^ 2 ≤ (4 * b + 10) * LL * (25 * L ^ 2) :=
    mul_le_mul hD hq (by positivity) (by nlinarith)
  have t2 : 16 * h ^ 2 ≤ 64 * L ^ 2 := by nlinarith
  have t3 : 64 * L ^ 2 ≤ 64 * (L ^ 2 * LL) := by
    have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ L ^ 2) hLL; linarith
  nlinarith

theorem hD_arith {e c b l LL : ℝ} (he : e = b * l) (hl : l ≤ 2 * LL) (hc : c ≤ 11) (hb : 1 ≤ b)
    (hLL : 1 ≤ LL) : 2 * e + c / 2 + 4 ≤ (4 * b + 10) * LL := by
  subst he
  have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ b)
  nlinarith

/-- The geometric and counting part of `thm:main`, assuming the required
product-profile instance of the smoothing lemma. -/
theorem of_smoothing (h : SmoothSectorCounting) : MainClaim := by
  obtain ⟨b₀, A, Cst, hd⟩ := Cubic.BoxAsymptotic.Pieces.hyp_data h
  obtain ⟨Kr, hKr, hred⟩ := Cubic.BoxAsymptotic.Reduction.reduction
  obtain ⟨Kd, hKd, hdisc⟩ := Cubic.BoxAsymptotic.Discard.discard
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  set b := A' / 2 + 1
  have hb1 : 1 ≤ b := by simp only [b]; linarith
  set a := |aStar|
  set k := |b₀ * Real.log 2 + aStar * c₁|
  have hpi : 0 < π := Real.pi_pos
  set CM := 18 * Real.sqrt 3 * (Real.log 2 / π) * (4 * a * Real.log 2 ^ 2 + k) * 30
  set C2 := 3 * 36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A' / 500
  set C3 := 36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * a * (25 * (4 * b + 10) + 64)
  set C4 := 36 * Real.sqrt 3 * (Real.log 2 / π) * k * 30
  have hCM : 0 ≤ CM := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  have hC4 : 0 ≤ C4 := by positivity
  refine ⟨Kr + Kd * (1 + 4 * b) / 6 + 28 * CM + C2 + C3 + C4, Real.exp 10, fun H hH => ?_⟩
  obtain ⟨hH3, hL10, hLL⟩ := log_facts hH
  have hH0 : 0 < H := by linarith
  set L := Real.log H
  set ε := (L ^ b)⁻¹
  obtain ⟨hε0, hεL, he, hε2⟩ := eps_facts hL10 hA'
  have hε1 : ε ≤ 1 / 10 :=
    hεL.trans (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  set LL := Real.log L
  -- the analytic inputs
  have r1 := hred H hH3
  have rd := hdisc H ε hH3 hε0 hε1
  have rb := Cubic.BoxAsymptotic.BulkSum.bulk (b₀ := b₀) (A := A) (Cst := Cst) hH3 hε0 hε1 hd
  have rs := Cubic.BoxAsymptotic.MainTerm.sum_absM (b₀ := b₀) hH3 hε0 hε1 (ε := ε)
  have rm := Cubic.BoxAsymptotic.MainTerm.main_eval (b₀ := b₀) hH3 hε0 hε1 (ε := ε)
  have rw0 : ∀ x ∈ Bset H, 0 ≤ W H x.1 (θ x.2) *
      (1 - (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2))) := fun x hx => by
    have h1 := (mem_Bset.mp (by simpa using hx : (x.1, x.2) ∈ Bset H)).1
    have hn : (0 : ℝ) < x.1 := by exact_mod_cast h1
    have := (Cubic.BoxAsymptotic.Core.wb_total_le (H := H) (ε := ε) (t := θ x.2) hn).2
    exact mul_nonneg (W_nonneg _ _ _) (by linarith)
  clear hd hred hdisc
  -- abbreviations
  set T := (1 / 6) * ∑ x ∈ Bset H, W H x.1 (θ x.2)
  set Tb := (1 / 6) * ∑ x ∈ Bset H, W H x.1 (θ x.2) *
    (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2))
  set Sd := ∑ x ∈ Bset H, W H x.1 (θ x.2) * (1 - (wb H ε 0 x.1 (θ x.2) + wb H ε π x.1 (θ x.2)))
  have eT : T - Tb = 1 / 6 * Sd := by
    simp only [T, Tb, Sd]; rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; exact Finset.sum_congr rfl fun x _ => by ring
  have hSd0 : 0 ≤ Sd := Finset.sum_nonneg rw0
  set S2 := 2 * ∑ p ∈ G H ε, M H b₀ p.1
  set SA := ∑ p ∈ G H ε, |M H b₀ p.1|
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hHL : 0 ≤ H * L ^ 2 := by positivity
  -- the six bounds
  have b1 : Kr * H * L ^ 2 ≤ Kr * (H * L ^ 2 * LL) := by
    have := le_LL (L := L) hKr.le hH0.le hLL; linarith
  have hlb : logb 2 L ≤ 2 * LL := logb_le_two_log (by linarith)
  have hl0 : 0 ≤ logb 2 L := logb_nonneg (by norm_num) (by linarith)
  have b2 : T - Tb ≤ Kd * (1 + 4 * b) / 6 * (H * L ^ 2 * LL) := by
    rw [eT]
    rw [he] at rd
    exact (mul_le_mul_of_nonneg_left rd (by norm_num)).trans
      (disc_arith hKd.le hH0.le hb1 hLL hlb)
  have hsM' : SA ≤ CM * (H * L ^ 3) := rs.trans (by
    simp only [CM]
    exact sM_arith (by positivity) hH0.le (abs_nonneg _) (by linarith))
  have b3 : 28 * ε * SA ≤ 28 * CM * (H * L ^ 2 * LL) :=
    e1_arith (by linarith) hεL hCM hH0.le hSA0 hsM' hLL
  have b4 : (1 + 14 * ε) * 36 * Real.sqrt 3 * |Cst| * (3 * L) ^ A' * (ε ^ 2 * H / 500) ≤
      C2 * (H * L ^ 2 * LL) := by
    have e3 : (3 * L) ^ A' = (3 : ℝ) ^ A' * L ^ A' := Real.mul_rpow (by norm_num) (by linarith)
    have h14 : 1 + 14 * ε ≤ 3 := by linarith
    have hx : 0 ≤ 36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A' := by positivity
    have e4 : (1 + 14 * ε) * 36 * Real.sqrt 3 * |Cst| * (3 * L) ^ A' * (ε ^ 2 * H / 500) =
        (1 + 14 * ε) * (36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A') * (L ^ A' * ε ^ 2) * (H / 500) := by
      rw [e3]; ring
    rw [e4]
    have a1 : (1 + 14 * ε) * (36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A') * (L ^ A' * ε ^ 2) ≤
        3 * (36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A') * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right h14 hx) hε2 (by positivity) (by positivity)
    have a2 : H ≤ H * L ^ 2 * LL := by
      have h1 : 1 ≤ L ^ 2 := one_le_pow₀ (by linarith)
      have : 1 ≤ L ^ 2 * LL := one_le_mul_of_one_le_of_one_le h1 hLL
      calc H = H * 1 := by ring
        _ ≤ H * (L ^ 2 * LL) := mul_le_mul_of_nonneg_left this hH0.le
        _ = H * L ^ 2 * LL := by ring
    calc (1 + 14 * ε) * (36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A') * (L ^ A' * ε ^ 2) * (H / 500)
        ≤ 3 * (36 * Real.sqrt 3 * |Cst| * (3 : ℝ) ^ A') * 1 * (H / 500) :=
          mul_le_mul_of_nonneg_right a1 (by positivity)
      _ = C2 * H := by simp only [C2]; ring
      _ ≤ C2 * (H * L ^ 2 * LL) := mul_le_mul_of_nonneg_left a2 hC2
  -- the main term errors
  have h2000 : logb 2 2000 ≤ 11 := by
    have := Cubic.BoxAsymptotic.Discard.logb_le_pow (by norm_num : (0 : ℝ) < 2000) (m := 11)
      (by norm_num)
    push_cast at this; exact this
  have hD : D ε ≤ (4 * b + 10) * LL := by
    simp only [D]
    exact hD_arith he hlb h2000 hb1 hLL
  have hh : logb 2 H ≤ 2 * L := logb_le_two_log (by linarith)
  have hh0 : 0 ≤ logb 2 H := logb_nonneg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D ε := by
    have := Cubic.BoxAsymptotic.GoodCount.e_nonneg hε0 hε1
    have : 0 ≤ logb 2 2000 := logb_nonneg (by norm_num) (by norm_num)
    simp only [D]; positivity
  have hm1 := hm1_arith hD hD0 hLL hh hh0 (by linarith)
  have b5 : 36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * a * H *
      (D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2) +
      36 * Real.sqrt 3 * (Real.log 2 / π) * H * k * (30 * L ^ 2) ≤
        C3 * (H * L ^ 2 * LL) + C4 * (H * L ^ 2 * LL) := by
    have t1 := mul_le_mul_of_nonneg_left hm1
      (by positivity : (0 : ℝ) ≤ 36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * a * H)
    have t2 := le_LL (L := L) hC4 hH0.le hLL
    have e1 : 36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * a * H *
        ((25 * (4 * b + 10) + 64) * (L ^ 2 * LL)) = C3 * (H * L ^ 2 * LL) := by
      simp only [C3]; ring
    have e2 : 36 * Real.sqrt 3 * (Real.log 2 / π) * H * k * (30 * L ^ 2) = C4 * (H * L ^ 2) := by
      simp only [C4]; ring
    linarith
  -- combine
  have hfin := combine r1 (by rw [eT]; positivity) b2 rb rm
  have e5 : (Kr + Kd * (1 + 4 * b) / 6 + 28 * CM + C2 + C3 + C4) * H * L ^ 2 * LL =
      Kr * (H * L ^ 2 * LL) + Kd * (1 + 4 * b) / 6 * (H * L ^ 2 * LL) +
        28 * CM * (H * L ^ 2 * LL) + C2 * (H * L ^ 2 * LL) +
          (C3 * (H * L ^ 2 * LL) + C4 * (H * L ^ 2 * LL)) := by ring
  rw [e5]
  refine hfin.trans ?_
  have hmain_rhs : 36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * |aStar| * H *
      (D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2) +
      36 * Real.sqrt 3 * (Real.log 2 / π) * H * |b₀ * Real.log 2 + aStar * c₁| * (30 * L ^ 2) ≤
        C3 * (H * L ^ 2 * LL) + C4 * (H * L ^ 2 * LL) := b5
  linarith

/-- All of `thm:main`, including its second constant formula and the final
two-sided order of growth. Only the six cited inputs from `lem:moment`
remain hypotheses; `lem:smooth` and its product-profile specialization
are proved and supplied here. -/
theorem «thm:main»
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    (hRM : CubicTargets.BoxAsymptotic.BinaryDecomposition.BlackBox)
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (hAFE : CubicTargets.BoxAsymptotic.GammaAFE.Identity)
    (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights)
    (hGamma : CubicTargets.BoxAsymptotic.GammaAFE.GammaRatio) :
    CubicTargets.BoxAsymptotic.FullMainClaim := by
  exact MainConsequences.complete (of_smoothing (SmoothProductCounting.of_full
    (SmoothSector.«lem:smooth» hLS hRM hHecke hAFE hWeights hGamma)))

end Cubic.BoxAsymptotic.MainTheorem
