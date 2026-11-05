import Cubic.Counting.TranslationClassData
import CubicTargets.Counting.TranslationClasses
import Cubic.Counting.GeneralTraceDecomposition
import Cubic.Counting.TraceZeroAsymptotic
import Cubic.Counting.EulerKroneckerCalculation
import Cubic.BoxAsymptotic.SquareDiscriminant

/-!
# Proof of `rem:translationClasses`

Following the remark. The invariant `I` is `n(f)`. Translating the roots by an integer `k`
changes the trace by `3k` and preserves `n`, so each translation class has exactly one
representative of trace `-1`, `0` or `1`. By `lemma:generalHeightReduction`, the
substitutions `f ↦ f` (trace `1`), `f ↦ -f(-t)` (trace `-1`) and `f ↦ f` (trace `0`) identify
these representatives with the polynomials counted by `A₁(Y)`, `A₁(Y)` and `A₀(Y/3)`, so
`C(Y) = 2A₁(Y) + A₀(Y/3)`. Substituting `eqn:A1asymptotic` and `prop:traceZeroAsymptotic`
gives the asymptotic for `C(Y)`, using that `Q` is linear with leading coefficient `2α/9`.
Since `f` has three distinct real roots, `4I³ - J² = 27 disc(f) > 0`, so `H_BS(f) = I³`;
setting `Y = H^{1/3}` gives `P_BS` and the error `O_ε(H^{1/6+ε})`.
-/

noncomputable section

namespace Cubic.Counting.TranslationClasses

open Polynomial Filter Asymptotics
open Cubic.Counting.GeneralMonicData Cubic.Counting.PolynomialCountData
open Cubic.Counting.TranslationClassData Cubic.Counting.GeneralHeightReduction
open Cubic.Counting.IntegralPointCountData
open CubicTargets.Counting.GeneralMonic
open CubicTargets.Counting.TranslationClasses (PBS)

/-! ### Translation -/

theorem translate_eq_signTranslate (k : ℤ) (f : ℤ[X]) : translate k f = signTranslate 1 k f := by
  simp [translate, signTranslate]

theorem translate_mem (k : ℤ) {f : ℤ[X]} (hf : f ∈ monicCyclic) : translate k f ∈ monicCyclic := by
  obtain ⟨⟨a₂, a₁, a₀, rfl⟩, hc⟩ := hf
  refine ⟨⟨_, _, _, translate_monicCubic k a₂ a₁ a₀⟩, ?_⟩
  rw [translate_eq_signTranslate]
  exact (cyclic_signTranslate_iff (Or.inl rfl) k (monicCubic_map_ne_zero _ _ _)).mpr hc

/-- Translating the roots by `-k` changes the trace by `-3k`. -/
theorem trace_translate (k : ℤ) {f : ℤ[X]} (hf : f ∈ monicCyclic) :
    trace (translate k f) = trace f - 3 * k := by
  obtain ⟨⟨a₂, a₁, a₀, rfl⟩, -⟩ := hf
  simp only [trace, translate_monicCubic, monicCubic_coeff_two]
  ring

/-! ### `I`, `J` and `H_BS` of a single polynomial -/

theorem polynomial_facts {f : ℤ[X]} (hf : f ∈ monicCyclic) :
    bsI f = invariant f ∧ 0 < bsI f ∧
      4 * bsI f ^ 3 - bsJ f ^ 2 = 27 * discriminant f ∧ 0 < discriminant f ∧
      bsHeight f = (bsI f : ℝ) ^ 3 := by
  obtain ⟨⟨a₂, a₁, a₀, rfl⟩, hc⟩ := hf
  have hI : bsI (monicCubic a₂ a₁ a₀) = a₂ ^ 2 - 3 * a₁ := by
    simp [bsI]
  have hJ : bsJ (monicCubic a₂ a₁ a₀) = -2 * a₂ ^ 3 + 9 * a₂ * a₁ - 27 * a₀ := by
    simp [bsJ]
  have hD : discriminant (monicCubic a₂ a₁ a₀) =
      Cubic.BoxAsymptotic.Parametrization.disc a₂ a₁ a₀ := by
    simp only [discriminant, _root_.Cubic.discr, monicCubic_coeff_two, monicCubic_coeff_one,
      monicCubic_coeff_zero, Cubic.BoxAsymptotic.Parametrization.disc]
    ring
  have hIpos : 0 < bsI (monicCubic a₂ a₁ a₀) := by rw [hI]; exact invariant_pos hc
  have hdisc : 4 * bsI (monicCubic a₂ a₁ a₀) ^ 3 - bsJ (monicCubic a₂ a₁ a₀) ^ 2 =
      27 * discriminant (monicCubic a₂ a₁ a₀) := by
    rw [hI, hJ, hD, Cubic.BoxAsymptotic.Parametrization.disc]; ring
  -- three real roots, distinct since the discriminant does not vanish
  have hDpos : 0 < discriminant (monicCubic a₂ a₁ a₀) := by
    have h0 := Cubic.BoxAsymptotic.SquareDiscriminant.disc_ne_zero_of_cyclic hc
    obtain ⟨x, y, z, h₂, h₁, h₀⟩ := real_roots hc
    have hsq : (Cubic.BoxAsymptotic.Parametrization.disc a₂ a₁ a₀ : ℝ) =
        ((x - y) * (x - z) * (y - z)) ^ 2 := by
      simp only [Cubic.BoxAsymptotic.Parametrization.disc]
      push_cast
      rw [h₂, h₁, h₀]; ring
    have hnn : (0 : ℝ) ≤ Cubic.BoxAsymptotic.Parametrization.disc a₂ a₁ a₀ := by
      rw [hsq]; positivity
    rw [hD]
    exact lt_of_le_of_ne (by exact_mod_cast hnn) (Ne.symm h0)
  refine ⟨by simp [bsI, invariant], hIpos, hdisc, hDpos, ?_⟩
  have hIr : (0 : ℝ) < bsI (monicCubic a₂ a₁ a₀) := by exact_mod_cast hIpos
  have hJr : ((bsJ (monicCubic a₂ a₁ a₀) : ℤ) : ℝ) ^ 2 / 4 ≤
      ((bsI (monicCubic a₂ a₁ a₀) : ℤ) : ℝ) ^ 3 := by
    have : (0 : ℝ) < 4 * (bsI (monicCubic a₂ a₁ a₀) : ℝ) ^ 3 -
        (bsJ (monicCubic a₂ a₁ a₀) : ℝ) ^ 2 := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hdisc
      push_cast at h
      have hd : (0 : ℝ) < discriminant (monicCubic a₂ a₁ a₀) := by exact_mod_cast hDpos
      rw [h]; linarith
    linarith
  rw [bsHeight, abs_of_pos hIr]
  exact max_eq_left hJr

theorem class_I_pos (c : TranslationClass) : 0 < c.I := by
  induction c using Quotient.ind with
  | _ f => exact (polynomial_facts f.2).2.1

theorem class_bsHeight (c : TranslationClass) : c.bsHeight = (c.I : ℝ) ^ 3 := by
  induction c using Quotient.ind with
  | _ f => exact (polynomial_facts f.2).2.2.2.2

/-! ### Representatives of trace `-1`, `0` or `1` -/

theorem mk_eq_mk {f g : monicCyclic} :
    TranslationClass.mk f = TranslationClass.mk g ↔ ∃ k : ℤ, (g : ℤ[X]) = translate k f :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem unique_representative (c : TranslationClass) :
    ∃! f : monicCyclic, TranslationClass.mk f = c ∧ trace f ∈ ({-1, 0, 1} : Set ℤ) := by
  induction c using Quotient.ind with
  | _ f =>
  set k := (trace (f : ℤ[X]) + 1) / 3
  have htr := trace_translate k f.2
  refine ⟨⟨translate k f, translate_mem k f.2⟩, ⟨(mk_eq_mk.mpr ⟨k, rfl⟩).symm, ?_⟩, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [htr]; omega
  · rintro g ⟨hg, hgtr⟩
    have hk : TranslationClass.mk ⟨translate k f, translate_mem k f.2⟩ = TranslationClass.mk g := by
      rw [hg]; exact (mk_eq_mk.mpr ⟨k, rfl⟩).symm
    obtain ⟨l, hl⟩ := mk_eq_mk.mp hk
    have hl' := trace_translate l (translate_mem k f.2)
    rw [← hl] at hl'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgtr
    have hl0 : l = 0 := by rw [htr] at hl'; omega
    apply Subtype.ext
    rw [hl, hl0, translate_zero]

/-! ### `C(Y) = 2A₁(Y) + A₀(Y/3)` -/

/-- The polynomials of `F_mon` of trace `s` with `n ≤ Y`. -/
def R (s : ℤ) (Y : ℝ) : Set ℤ[X] := {f | f ∈ monicCyclic ∧ trace f = s ∧ (invariant f : ℝ) ≤ Y}

theorem bijOn_one {s ε : ℤ} (hs : ¬ 3 ∣ s) (hε : ε = 1 ∨ ε = -1) (hmod : ε * s ≡ 1 [ZMOD 3])
    (Y : ℝ) : Set.BijOn (signTranslate ε ((ε * s - 1) / 3)) (R s Y) (traceOneSet Y) := by
  obtain ⟨-, h1, -⟩ := «lemma:generalHeightReduction»
  refine ⟨?_, (GeneralTraceDecomposition.signTranslate_injective hε _).injOn, ?_⟩
  · rintro f ⟨hf, htr, hY⟩
    obtain ⟨hg, hn⟩ := (h1 s (invariant f) ε hs hε hmod).mapsTo ⟨hf, htr, rfl⟩
    exact ⟨hg, by rw [hn]; exact hY⟩
  · rintro g ⟨hg, hY⟩
    obtain ⟨f, ⟨hf, htr, hn⟩, rfl⟩ := (h1 s (1 - 3 * g.coeff 1) ε hs hε hmod).surjOn ⟨hg, rfl⟩
    exact ⟨f, ⟨hf, htr, by rw [hn]; exact hY⟩, rfl⟩

theorem bijOn_zero (Y : ℝ) :
    Set.BijOn (signTranslate 1 (0 / 3)) (R 0 Y) (traceZeroSet (Y / 3)) := by
  obtain ⟨h0, -, h2⟩ := «lemma:generalHeightReduction»
  refine ⟨?_, (GeneralTraceDecomposition.signTranslate_injective (Or.inl rfl) _).injOn, ?_⟩
  · rintro f ⟨hf, htr, hY⟩
    obtain ⟨N, c, hnN, hg, hc⟩ := (h2 0 (invariant f) (dvd_zero 3)).mapsTo ⟨hf, htr, rfl⟩
    have hpos := (h0 f hf).1
    rw [hnN] at hpos hY
    refine ⟨N, c, hg, by omega, ?_, hg ▸ hc⟩
    push_cast at hY; linarith
  · rintro g ⟨N, c, rfl, hN1, hNY, hc⟩
    obtain ⟨f, ⟨hf, htr, hn⟩, hfg⟩ := (h2 0 (3 * N) (dvd_zero 3)).surjOn ⟨N, c, rfl, rfl, hc⟩
    refine ⟨f, ⟨hf, htr, ?_⟩, hfg⟩
    rw [hn]; push_cast; linarith

theorem R_card_one (Y : ℝ) : (R 1 Y).Finite ∧ Nat.card (R 1 Y) = A₁ Y := by
  have h := bijOn_one (s := 1) (ε := 1) (by decide) (Or.inl rfl) (by decide) Y
  exact ⟨Set.Finite.of_finite_image (h.image_eq ▸ A1Asymptotic.traceOneSet_finite _) h.injOn,
    Nat.card_congr h.equiv⟩

theorem R_card_neg_one (Y : ℝ) : (R (-1) Y).Finite ∧ Nat.card (R (-1) Y) = A₁ Y := by
  have h := bijOn_one (s := -1) (ε := -1) (by decide) (Or.inr rfl) (by decide) Y
  exact ⟨Set.Finite.of_finite_image (h.image_eq ▸ A1Asymptotic.traceOneSet_finite _) h.injOn,
    Nat.card_congr h.equiv⟩

theorem R_card_zero (Y : ℝ) : (R 0 Y).Finite ∧ Nat.card (R 0 Y) = A₀ (Y / 3) := by
  have h := bijOn_zero Y
  exact ⟨Set.Finite.of_finite_image
    (h.image_eq ▸ TraceZeroSplitting.traceZeroSet_finite _) h.injOn, Nat.card_congr h.equiv⟩

/-- The representatives of trace `-1`, `0` or `1` with `I ≤ Y`. -/
def reps (Y : ℝ) : Set monicCyclic :=
  {f | trace (f : ℤ[X]) ∈ ({-1, 0, 1} : Set ℤ) ∧ (invariant (f : ℤ[X]) : ℝ) ≤ Y}

theorem reps_bijOn (Y : ℝ) : Set.BijOn TranslationClass.mk (reps Y) (classesUpTo Y) := by
  refine ⟨fun f hf => hf.2, ?_, ?_⟩
  · intro f hf g hg hfg
    exact (unique_representative (TranslationClass.mk f)).unique ⟨rfl, hf.1⟩ ⟨hfg.symm, hg.1⟩
  · intro c hc
    obtain ⟨f, ⟨hfc, hftr⟩, -⟩ := unique_representative c
    refine ⟨f, ⟨hftr, ?_⟩, hfc⟩
    have : (c.I : ℝ) ≤ Y := hc
    rw [← hfc, TranslationClass.I_mk] at this
    exact this

theorem val_image_reps (Y : ℝ) :
    Subtype.val '' reps Y = R (-1) Y ∪ R 0 Y ∪ R 1 Y := by
  ext f
  constructor
  · rintro ⟨g, ⟨htr, hY⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htr
    rcases htr with h | h | h
    · exact Or.inl (Or.inl ⟨g.2, h, hY⟩)
    · exact Or.inl (Or.inr ⟨g.2, h, hY⟩)
    · exact Or.inr ⟨g.2, h, hY⟩
  · rintro ((h | h) | h) <;>
      exact ⟨⟨f, h.1⟩, ⟨by simp [h.2.1], h.2.2⟩, rfl⟩

theorem disjoint_R {s t : ℤ} (hst : s ≠ t) (Y : ℝ) : Disjoint (R s Y) (R t Y) :=
  Set.disjoint_left.mpr fun _ hs ht => hst (hs.2.1.symm.trans ht.2.1)

theorem class_count (Y : ℝ) :
    (classesUpTo Y).Finite ∧ classCount Y = 2 * A₁ Y + A₀ (Y / 3) := by
  have hb := reps_bijOn Y
  have hv : Set.BijOn Subtype.val (reps Y) (Subtype.val '' reps Y) :=
    Subtype.val_injective.injOn.bijOn_image
  obtain ⟨fm, cm⟩ := R_card_neg_one Y
  obtain ⟨f0, c0⟩ := R_card_zero Y
  obtain ⟨f1, c1⟩ := R_card_one Y
  have hU : (Subtype.val '' reps Y).Finite := by
    rw [val_image_reps]; exact (fm.union f0).union f1
  have hrf : (reps Y).Finite := Set.Finite.of_finite_image hU Subtype.val_injective.injOn
  refine ⟨hb.image_eq ▸ hrf.image _, ?_⟩
  rw [classCount, ← Nat.card_congr hb.equiv, Nat.card_congr hv.equiv, val_image_reps,
    Nat.card_coe_set_eq, Set.ncard_union_eq _ (fm.union f0) f1,
    Set.ncard_union_eq (disjoint_R (by decide) Y) fm f0]
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, cm, c0, c1]
    ring
  · exact Set.disjoint_union_left.mpr ⟨disjoint_R (by decide) Y, disjoint_R (by decide) Y⟩

/-! ### The asymptotic for `C(Y)` -/

theorem main_identity (μ : ℂ) {Y : ℝ} (hY : 0 < Y) :
    2 * (1 / 2 * Y * Q μ (1 / 2 * Real.log Y) - Real.pi / (9 * Real.sqrt 3) * Y) +
      (5 / 2 * (Y / 3) * Q μ (1 / 2 * Real.log (Y / 3)) -
        (alpha / 4 * Real.log 3 + Real.pi / (3 * Real.sqrt 3)) * (Y / 3)) =
      Y * (11 / 6 * Q μ (1 / 2 * Real.log Y) - 19 * alpha / 108 * Real.log 3 -
        Real.pi / (3 * Real.sqrt 3)) := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [Real.log_div hY.ne' (by norm_num)]
  simp only [Q]
  field_simp
  ring

theorem class_asymptotic
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    HasMainTerm (fun Y => (classCount Y : ℝ))
      (fun Y => Y * (11 / 6 * Q EulerKroneckerCalculation.value (1 / 2 * Real.log Y) -
        19 * alpha / 108 * Real.log 3 - Real.pi / (3 * Real.sqrt 3))) := by
  obtain ⟨-, hA1⟩ := A1Asymptotic.«eqn:A1asymptotic» hPoisson hCN
  obtain ⟨-, hA0⟩ := TraceZeroAsymptotic.«prop:traceZeroAsymptotic» hPoisson hCN
  intro ε hε
  obtain ⟨K₁, X₁, h₁⟩ := hA1 ε hε
  obtain ⟨K₀, X₀, h₀⟩ := hA0 ε hε
  refine ⟨2 * |K₁| + |K₀|, max (max X₁ (3 * X₀)) 1, fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := by linarith
  have e1 := h₁ Y (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY)
  have e0 := h₀ (Y / 3) (by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY; linarith)
  have hr : 0 < 1 / 2 + ε := by linarith
  have hpow : (Y / 3) ^ (1 / 2 + ε) ≤ Y ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hr.le
  have hP : 0 ≤ Y ^ (1 / 2 + ε) := by positivity
  have hP3 : 0 ≤ (Y / 3) ^ (1 / 2 + ε) := by positivity
  have b1 : K₁ * Y ^ (1 / 2 + ε) ≤ |K₁| * Y ^ (1 / 2 + ε) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hP
  have b0 : K₀ * (Y / 3) ^ (1 / 2 + ε) ≤ |K₀| * Y ^ (1 / 2 + ε) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hP3).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
  beta_reduce at e1 e0 ⊢
  rw [(class_count Y).2, ← main_identity _ hY0]
  push_cast
  rw [abs_le] at e1 e0 ⊢
  constructor <;> nlinarith [e1.1, e1.2, e0.1, e0.2]

/-! ### `H_BS = I³` and `Y = H^{1/3}` -/

theorem bsClasses_subset (H : ℝ) : bsClasses H ⊆ classesUpTo H := by
  intro c hc
  have h1 : (1 : ℝ) ≤ c.I := by exact_mod_cast class_I_pos c
  have : (c.I : ℝ) ^ 3 ≤ H := by rw [← class_bsHeight]; exact hc
  show (c.I : ℝ) ≤ H
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c.I) (by linarith : (0 : ℝ) ≤ c.I - 1))
    (by linarith : (0 : ℝ) ≤ c.I + 1)]

theorem bsClasses_eq {H : ℝ} (hH : 0 ≤ H) : bsClasses H = classesUpTo (H ^ (1 / 3 : ℝ)) := by
  ext c
  have h0 : (0 : ℝ) ≤ c.I := by exact_mod_cast (class_I_pos c).le
  have hc : (H ^ (1 / 3 : ℝ)) ^ 3 = H := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hH (by norm_num)
  show c.bsHeight ≤ H ↔ (c.I : ℝ) ≤ H ^ (1 / 3 : ℝ)
  rw [class_bsHeight, ← pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0), hc]

theorem PBS_eq (μ : ℂ) (X : ℝ) :
    11 / 6 * Q μ (1 / 2 * (1 / 3 * X)) - 19 * alpha / 108 * Real.log 3 -
      Real.pi / (3 * Real.sqrt 3) = PBS μ X := by
  simp only [Q, PBS]
  ring

theorem «rem:translationClasses»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.TranslationClasses.Claim := by
  have hC := class_asymptotic hPoisson hCN
  refine ⟨_, _, EulerKroneckerCalculation.genuine_constant, fun f hf => polynomial_facts hf,
    unique_representative, class_count, hC,
    fun H => (class_count H).1.subset (bsClasses_subset H), fun ε hε => ?_⟩
  obtain ⟨K, X₀, hK⟩ := hC ε hε
  refine Asymptotics.IsBigO.of_bound |K| ?_
  rw [Filter.eventually_atTop]
  refine ⟨max 1 (|X₀| ^ 3), fun H hH => ?_⟩
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) hH
  have hH0 : 0 < H := by linarith
  set Y := H ^ (1 / 3 : ℝ) with hYdef
  have hY : X₀ ≤ Y := by
    have h3 : |X₀| ^ 3 ≤ H := le_trans (le_max_right _ _) hH
    have hc : Y ^ 3 = H := by
      rw [hYdef, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hH0.le (by norm_num)
    have hY0 : 0 ≤ Y := by positivity
    have : |X₀| ≤ Y := by
      rw [← pow_le_pow_iff_left₀ (abs_nonneg _) hY0 (by norm_num : (3 : ℕ) ≠ 0), hc]; exact h3
    exact (le_abs_self _).trans this
  have hb := hK Y hY
  beta_reduce at hb
  have hlog : Real.log Y = 1 / 3 * Real.log H := by
    rw [hYdef, Real.log_rpow hH0]
  rw [hlog, PBS_eq] at hb
  have hcount : bsCount H = classCount Y := by
    rw [bsCount, classCount, bsClasses_eq hH0.le]
  have hexp : Y ^ (1 / 2 + ε) ≤ H ^ (1 / 6 + ε) := by
    rw [hYdef, ← Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow_of_exponent_le hH1 (by nlinarith)
  have hP : 0 < H ^ (1 / 6 + ε) := Real.rpow_pos_of_pos hH0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP, hcount]
  calc _ ≤ K * Y ^ (1 / 2 + ε) := hb
    _ ≤ |K| * Y ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |K| * H ^ (1 / 6 + ε) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)

end Cubic.Counting.TranslationClasses
