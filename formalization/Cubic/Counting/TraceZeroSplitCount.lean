import Cubic.Counting.CenteredEllipseCount
import Cubic.Counting.TraceZeroSplitting
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Split trace-zero cubics

Supporting count for `prop:traceZeroAsymptotic`, following the paper: the split cubics
`t³ - Nt + c` are parametrized by the `S₃`-orbits of integer triples `(x, y, -x-y)` of roots,
with `N = x² + xy + y²`. The ellipse `x² + xy + y² ≤ X` contains `2πX/√3 + O(X^{1/2})`
lattice points; every nonidentity permutation fixes only triples with two equal entries, of
which there are `O(X^{1/2})`; so Burnside's lemma gives
`#{split t³ - Nt + c : 1 ≤ N ≤ X} = πX/(3√3) + O(X^{1/2})`.
-/

noncomputable section

namespace Cubic.Counting.TraceZeroSplitCount

open Polynomial Cubic.Counting.GeneralMonicData Cubic.Counting.TraceZeroSplitting
open Cubic.Counting.GeneralHeightReduction

/-- Two triples with the same entries up to order differ by a permutation. -/
theorem exists_perm {v w : Fin 3 → ℤ} (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin 3), w = v ∘ σ := by
  have hs : v ∘ Tuple.sort v = w ∘ Tuple.sort w := List.ofFn_injective
    (List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort v))
      (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort w))
      (((Tuple.sort v).ofFn_comp_perm v).trans (h.trans ((Tuple.sort w).ofFn_comp_perm w).symm)))
  refine ⟨(Tuple.sort w).symm.trans (Tuple.sort v), funext fun i => ?_⟩
  have := congrFun hs ((Tuple.sort w).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  simpa using this.symm

/-- Nonzero integer triples `(x, y, z)` with `x + y + z = 0` and `x² + y² + z² ≤ 2X`, i.e.
`x² + xy + y² ≤ X`. -/
def Triples (X : ℝ) : Set (Fin 3 → ℤ) :=
  {v | ∑ i, v i = 0 ∧ v ≠ 0 ∧ ((∑ i, v i ^ 2 : ℤ) : ℝ) ≤ 2 * X}

/-- `S₃` permutes the entries. -/
instance (X : ℝ) : MulAction (Equiv.Perm (Fin 3)) (Triples X) where
  smul σ v := ⟨fun i => v.1 (σ⁻¹ i), by
    obtain ⟨v, h0, h1, h2⟩ := v
    refine ⟨?_, ?_, ?_⟩
    · rw [Equiv.sum_comp σ⁻¹ v]; exact h0
    · intro h; apply h1; funext i; simpa using congrFun h (σ i)
    · rw [Equiv.sum_comp σ⁻¹ (fun i => v i ^ 2)]; exact h2⟩
  one_smul v := rfl
  mul_smul σ τ v := rfl

theorem smul_apply {X : ℝ} (σ : Equiv.Perm (Fin 3)) (v : Triples X) (i : Fin 3) :
    (σ • v).1 i = v.1 (σ⁻¹ i) := rfl

/-- The cubic `∏ (t - vᵢ)` with the entries of `v` as roots. -/
def cubicOf (v : Fin 3 → ℤ) : ℤ[X] := ∏ i, (X - C (v i))

theorem cubicOf_smul {Y : ℝ} (σ : Equiv.Perm (Fin 3)) (v : Triples Y) :
    cubicOf (σ • v).1 = cubicOf v.1 := by
  simp only [cubicOf, smul_apply]
  exact Equiv.prod_comp σ⁻¹ (fun i => X - C (v.1 i))

theorem cubicOf_eq {v : Fin 3 → ℤ} (h : ∑ i, v i = 0) :
    cubicOf v = monicCubic 0 (-(v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2)) (v 0 * v 1 * (v 0 + v 1)) := by
  rw [Fin.sum_univ_three] at h
  have h2 : v 2 = -v 0 - v 1 := by linarith
  simp only [cubicOf, Fin.prod_univ_three, monicCubic, h2]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_zero]
  ring

theorem sum_sq_eq {v : Fin 3 → ℤ} (h : ∑ i, v i = 0) :
    ∑ i, v i ^ 2 = 2 * (v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2) := by
  rw [Fin.sum_univ_three] at h ⊢
  have h2 : v 2 = -v 0 - v 1 := by linarith
  rw [h2]; ring

theorem roots_cubicOf (v : Fin 3 → ℤ) :
    (cubicOf v).roots = (List.ofFn v : Multiset ℤ) := by
  rw [cubicOf, Fin.prod_univ_three, roots_mul, roots_mul, roots_X_sub_C, roots_X_sub_C,
    roots_X_sub_C]
  · simp [List.ofFn_succ]; rfl
  all_goals
    simp only [ne_eq, mul_eq_zero, X_sub_C_ne_zero, or_self, not_false_eq_true]

theorem norm_pos_of_mem {Y : ℝ} {v : Fin 3 → ℤ} (hv : v ∈ Triples Y) :
    1 ≤ v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2 := by
  obtain ⟨h0, h1, -⟩ := hv
  rw [Fin.sum_univ_three] at h0
  by_contra hlt
  have hle : v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2 ≤ 0 := by omega
  have ha : v 0 = 0 := by nlinarith [sq_nonneg (v 0 + 2 * v 1), sq_nonneg (2 * v 0 + v 1)]
  have hb : v 1 = 0 := by nlinarith [sq_nonneg (v 0 + 2 * v 1), sq_nonneg (2 * v 0 + v 1)]
  have hc : v 2 = 0 := by omega
  apply h1
  funext i
  fin_cases i <;> simp [ha, hb, hc]

theorem cubicOf_mem {Y : ℝ} (v : Triples Y) : cubicOf v.1 ∈ splitSet Y := by
  obtain ⟨v, hv⟩ := v
  refine ⟨v 0 ^ 2 + v 0 * v 1 + v 1 ^ 2, v 0 * v 1 * (v 0 + v 1), cubicOf_eq hv.1,
    norm_pos_of_mem hv, ?_, ?_⟩
  · have h := hv.2.2
    rw [sum_sq_eq hv.1] at h
    push_cast at h ⊢; linarith
  · rw [cubicOf, Fin.prod_univ_three]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact ((Splits.X_sub_C ((Int.castRingHom ℚ) (v 0))).mul
      (Splits.X_sub_C ((Int.castRingHom ℚ) (v 1)))).mul (Splits.X_sub_C ((Int.castRingHom ℚ) (v 2)))

/-- Orbits of triples correspond to the polynomials with those roots. -/
def orbitMap (Y : ℝ) :
    MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples Y) → splitSet Y :=
  Quotient.lift (fun v => ⟨cubicOf v.1, cubicOf_mem v⟩) (by
    rintro v w ⟨σ, rfl⟩
    exact Subtype.ext (cubicOf_smul σ w))

theorem orbitMap_injective (Y : ℝ) : Function.Injective (orbitMap Y) := by
  rintro ⟨v⟩ ⟨w⟩ h
  have h' : cubicOf v.1 = cubicOf w.1 := congrArg Subtype.val h
  have hr := congrArg Polynomial.roots h'
  rw [roots_cubicOf, roots_cubicOf, Multiset.coe_eq_coe] at hr
  obtain ⟨σ, hσ⟩ := exists_perm hr
  apply Quotient.sound
  refine ⟨σ, Subtype.ext (funext fun i => ?_)⟩
  rw [smul_apply, hσ]; simp

theorem monicCubic_monic (a₂ a₁ a₀ : ℤ) : (monicCubic a₂ a₁ a₀).Monic := by
  unfold monicCubic; monicity!

theorem orbitMap_surjective (Y : ℝ) : Function.Surjective (orbitMap Y) := by
  rintro ⟨g, N, c, rfl, hN, hNY, hs⟩
  have ha : (cubicData N c).a ≠ 0 := one_ne_zero
  have hs' : ((cubicData N c).toPoly.map (RingHom.id ℚ)).Splits := by
    rw [Polynomial.map_id, toPoly_cubicData]; exact hs
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three ha).mp hs'
  have hb := _root_.Cubic.b_eq_three_roots ha h3
  have hc := _root_.Cubic.c_eq_three_roots ha h3
  have hd := _root_.Cubic.d_eq_three_roots ha h3
  simp only [cubicData, RingHom.id_apply, one_mul] at hb hc hd
  -- the roots are integers
  have hint : ∀ r : ℚ, r ∈ ({x, y, z} : Multiset ℚ) → ∃ m : ℤ, (m : ℚ) = r := by
    intro r hr
    rw [← h3, _root_.Cubic.roots, _root_.Cubic.map_toPoly, Polynomial.map_id,
      toPoly_cubicData, mem_roots ((monicCubic_monic _ _ _).map _).ne_zero, IsRoot.def] at hr
    have hr' : aeval r (monicCubic 0 (-N) c) = 0 := by
      rw [aeval_def, ← hr, eval_map]; rfl
    obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic (monicCubic_monic 0 (-N) c) hr'
    exact ⟨m, hm⟩
  obtain ⟨p, rfl⟩ := hint x (by simp)
  obtain ⟨q, rfl⟩ := hint y (by simp)
  obtain ⟨t, rfl⟩ := hint z (by simp)
  have hb' : p + q + t = 0 := by exact_mod_cast (by linarith : (p + q + t : ℚ) = 0)
  have hc' : -N = p * q + p * t + q * t := by exact_mod_cast (by push_cast at hc ⊢; linarith :
    ((-N : ℤ) : ℚ) = p * q + p * t + q * t)
  have hd' : c = -(p * q * t) := by exact_mod_cast (by linarith :
    ((c : ℤ) : ℚ) = -(p * q * t))
  have ht : t = -p - q := by linarith
  subst ht
  have hN' : N = p ^ 2 + p * q + q ^ 2 := by linear_combination -hc'
  let v : Fin 3 → ℤ := ![p, q, -p - q]
  have hv0 : ∑ i, v i = 0 := by simp [v, Fin.sum_univ_three]
  have hv : v ∈ Triples Y := by
    refine ⟨hv0, ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 0
      have h2 := congrFun h0 1
      simp [v] at h1 h2
      rw [h1, h2] at hN'; omega
    · rw [sum_sq_eq hv0]
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hN']; push_cast; linarith
  refine ⟨Quotient.mk _ ⟨v, hv⟩, Subtype.ext ?_⟩
  show cubicOf v = _
  rw [cubicOf_eq hv0]
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hN', hd']; congr 1; ring

theorem card_orbits (Y : ℝ) :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples Y)) =
      Nat.card (splitSet Y) :=
  Nat.card_congr (Equiv.ofBijective _ ⟨orbitMap_injective Y, orbitMap_surjective Y⟩)

/-! ### Burnside's lemma -/

open CenteredEllipseCount in
theorem pair_mem {Y : ℝ} {v : Fin 3 → ℤ} (hv : v ∈ Triples Y) : (v 0, v 1) ∈ points Y := by
  have h := hv.2.2
  rw [sum_sq_eq hv.1] at h
  show form ((v 0 : ℝ), (v 1 : ℝ)) ≤ Y
  simp only [form]; push_cast at h; linarith

theorem pair_injOn (Y : ℝ) : Set.InjOn (fun v : Fin 3 → ℤ => (v 0, v 1)) (Triples Y) := by
  intro v hv w hw h
  simp only [Prod.mk.injEq] at h
  have hv0 := hv.1; have hw0 := hw.1
  rw [Fin.sum_univ_three] at hv0 hw0
  funext i; fin_cases i
  · exact h.1
  · exact h.2
  · show v 2 = w 2; omega

open CenteredEllipseCount in
theorem image_pair (Y : ℝ) :
    (fun v : Fin 3 → ℤ => (v 0, v 1)) '' Triples Y = points Y \ {0} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨v, hv, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨pair_mem hv, fun h0 => ?_⟩
    simp only [Set.mem_singleton_iff, Prod.mk_eq_zero] at h0
    have := norm_pos_of_mem hv
    rw [h0.1, h0.2] at this; omega
  · rintro ⟨hp, hp0⟩
    have hv0 : ∑ i, (![a, b, -a - b] : Fin 3 → ℤ) i = 0 := by simp [Fin.sum_univ_three]
    refine ⟨![a, b, -a - b], ⟨hv0, ?_, ?_⟩, rfl⟩
    · intro h0
      apply hp0
      have h1 := congrFun h0 0
      have h2 := congrFun h0 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
      simp [h1, h2]
    · have hp' : form ((a : ℝ), (b : ℝ)) ≤ Y := hp
      rw [sum_sq_eq hv0]
      simp only [form, Matrix.cons_val_zero, Matrix.cons_val_one] at hp' ⊢
      push_cast; linarith

theorem triples_finite (Y : ℝ) : (Triples Y).Finite :=
  Set.Finite.of_finite_image ((CenteredEllipseCount.points_finite Y).subset
    (by rintro _ ⟨v, hv, rfl⟩; exact pair_mem hv)) (pair_injOn Y)

theorem ncard_triples {Y : ℝ} (hY : 0 ≤ Y) :
    (Triples Y).ncard + 1 = Nat.card (CenteredEllipseCount.points Y) := by
  have h0 : (0 : ℤ × ℤ) ∈ CenteredEllipseCount.points Y := by
    simp [CenteredEllipseCount.points, CenteredEllipseCount.form, hY]
  rw [← (pair_injOn Y).ncard_image, image_pair Y,
    Set.ncard_diff_singleton_add_one h0 (CenteredEllipseCount.points_finite Y),
    Nat.card_coe_set_eq]

/-- A nonidentity permutation fixes only triples with two equal entries. -/
theorem two_equal_of_fixed {Y : ℝ} {σ : Equiv.Perm (Fin 3)} (hσ : σ ≠ 1) {v : Triples Y}
    (hv : σ • v = v) : v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2 := by
  obtain ⟨i, hi⟩ : ∃ i, σ⁻¹ i ≠ i := by
    by_contra h
    push_neg at h
    exact hσ (inv_eq_one.mp (Equiv.ext h))
  have he : v.1 (σ⁻¹ i) = v.1 i := by
    rw [← smul_apply]; exact congrFun (congrArg Subtype.val hv) i
  generalize σ⁻¹ i = j at hi he
  fin_cases i <;> fin_cases j <;> simp at hi he ⊢ <;> tauto

/-- The triples with two equal entries: at most `3(2⌊2√Y⌋ + 1)` of them. -/
theorem ncard_two_equal_le (Y : ℝ) :
    {v : Triples Y | v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2}.ncard ≤
      (2 * ⌊2 * √Y⌋.toNat + 1) * 3 := by
  classical
  set B := ⌊2 * √Y⌋
  let φ : Triples Y → ℤ × Fin 3 := fun v =>
    if v.1 0 = v.1 1 then (v.1 0, 0) else if v.1 0 = v.1 2 then (v.1 0, 1) else (v.1 1, 2)
  have hbound : ∀ (v : Triples Y) (k : Fin 3), -B ≤ v.1 k ∧ v.1 k ≤ B := by
    intro v k
    have hs := v.2.2.2
    have h0 := v.2.1
    rw [Fin.sum_univ_three] at h0
    have hsq : ((v.1 k : ℤ) : ℝ) ^ 2 ≤ (2 * √Y) ^ 2 := by
      have hY : 0 ≤ Y := by
        have : (0 : ℝ) ≤ ((∑ i, v.1 i ^ 2 : ℤ) : ℝ) := by positivity
        linarith
      rw [mul_pow, Real.sq_sqrt hY]
      have hk : (v.1 k) ^ 2 ≤ 2 * ∑ i, v.1 i ^ 2 := by
        rw [Fin.sum_univ_three]
        fin_cases k <;> simp <;> nlinarith [sq_nonneg (v.1 0 - v.1 1), sq_nonneg (v.1 0 - v.1 2),
          sq_nonneg (v.1 1 - v.1 2)]
      have : ((v.1 k ^ 2 : ℤ) : ℝ) ≤ 2 * ((∑ i, v.1 i ^ 2 : ℤ) : ℝ) := by exact_mod_cast hk
      push_cast at this hs ⊢; nlinarith
    have habs := sq_le_sq.mp hsq
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * √Y), abs_le] at habs
    constructor
    · have : -v.1 k ≤ B := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr habs.2
  let S : Finset (ℤ × Fin 3) := Finset.Icc (-B) B ×ˢ Finset.univ
  have hmaps : Set.MapsTo φ {v : Triples Y | v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2}
      (S : Set (ℤ × Fin 3)) := by
    intro v _
    simp only [φ, S, Finset.coe_product, Finset.coe_Icc, Finset.coe_univ, Set.mem_prod,
      Set.mem_Icc, Set.mem_univ, and_true]
    split_ifs <;> exact hbound _ _
  have hinj : Set.InjOn φ {v : Triples Y | v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2} := by
    intro v hv w hw h
    have hv0 := v.2.1
    have hw0 := w.2.1
    rw [Fin.sum_univ_three] at hv0 hw0
    simp only [Set.mem_setOf_eq] at hv hw
    apply Subtype.ext
    funext k
    simp only [φ] at h
    split_ifs at h <;> simp [Prod.ext_iff] at h <;> fin_cases k <;> simp <;> omega
  calc _ ≤ (S : Set (ℤ × Fin 3)).ncard := Set.ncard_le_ncard_of_injOn φ hmaps hinj S.finite_toSet
    _ = (B + 1 - -B).toNat * 3 := by
        rw [Set.ncard_coe_finset, Finset.card_product, Int.card_Icc, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ (2 * B.toNat + 1) * 3 := by
        apply Nat.mul_le_mul_right; omega

/-- Burnside's lemma: `6 · #orbits = #triples + Σ_{σ ≠ 1} #Fix(σ)`, and each nonidentity
term is at most the number of triples with two equal entries. -/
theorem burnside_bounds (Y : ℝ) :
    (Triples Y).ncard ≤ 6 * Nat.card (splitSet Y) ∧
      6 * Nat.card (splitSet Y) ≤ (Triples Y).ncard + 5 * ((2 * ⌊2 * √Y⌋.toNat + 1) * 3) := by
  classical
  haveI : Fintype (Triples Y) := (triples_finite Y).fintype
  haveI : ∀ σ : Equiv.Perm (Fin 3), Fintype (MulAction.fixedBy (Triples Y) σ) :=
    fun _ => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples Y)) :=
    Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin 3)) (Triples Y)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card, card_orbits,
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ 1)] at hB
  have h1 : Fintype.card (MulAction.fixedBy (Triples Y) (1 : Equiv.Perm (Fin 3))) =
      (Triples Y).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun v => MulAction.mem_fixedBy.mpr (one_smul _ v))), Nat.card_coe_set_eq]
  have hfix : ∀ σ ∈ Finset.univ \ {(1 : Equiv.Perm (Fin 3))},
      Fintype.card (MulAction.fixedBy (Triples Y) σ) ≤ (2 * ⌊2 * √Y⌋.toNat + 1) * 3 := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := by simpa using hσ
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    refine le_trans (Set.ncard_le_ncard (fun v hv => two_equal_of_fixed hσ1 hv)
      (Set.toFinite _)) (ncard_two_equal_le Y)
  have hsum := Finset.sum_le_card_nsmul _ _ _ hfix
  have hcard : (Finset.univ \ {(1 : Equiv.Perm (Fin 3))}).card = 5 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_perm]; simp [Nat.factorial]
  rw [hcard, smul_eq_mul] at hsum
  rw [h1, show Nat.factorial 3 = 6 from rfl] at hB
  constructor <;> omega

/-- `#{split t³ - Nt + c : 1 ≤ N ≤ X} = πX/(3√3) + O(X^{1/2})`. -/
theorem split_count : ∃ K : ℝ, ∀ Y : ℝ, 1 ≤ Y →
    |(Nat.card (splitSet Y) : ℝ) - Real.pi / (3 * √3) * Y| ≤ K * √Y := by
  obtain ⟨K₀, hK₀⟩ := CenteredEllipseCount.count_bound
  refine ⟨(K₀ + 1 + 15 * 5) / 6, fun Y hY => ?_⟩
  have hY0 : 0 ≤ Y := by linarith
  have hsY : 1 ≤ √Y := Real.one_le_sqrt.mpr hY
  have hP := hK₀ Y hY
  have hT := ncard_triples hY0
  obtain ⟨hlo, hhi⟩ := burnside_bounds Y
  have hB : ((⌊2 * √Y⌋.toNat : ℕ) : ℝ) ≤ 2 * √Y := by
    have h0 : (0 : ℝ) ≤ 2 * √Y := by positivity
    rcases le_or_gt 0 ⌊2 * √Y⌋ with h | h
    · have : ((⌊2 * √Y⌋.toNat : ℕ) : ℤ) = ⌊2 * √Y⌋ := Int.toNat_of_nonneg h
      have h' : (((⌊2 * √Y⌋.toNat : ℕ) : ℤ) : ℝ) = ((⌊2 * √Y⌋ : ℤ) : ℝ) := by rw [this]
      push_cast at h'; rw [h']; exact Int.floor_le _
    · rw [Int.toNat_of_nonpos h.le]; simp only [CharP.cast_eq_zero]; exact h0
  have hlo' : ((Triples Y).ncard : ℝ) ≤ 6 * Nat.card (splitSet Y) := by exact_mod_cast hlo
  have hhi' : (6 * Nat.card (splitSet Y) : ℝ) ≤
      (Triples Y).ncard + 5 * ((2 * (⌊2 * √Y⌋.toNat : ℝ) + 1) * 3) := by exact_mod_cast hhi
  have hT' : ((Triples Y).ncard : ℝ) + 1 = Nat.card (CenteredEllipseCount.points Y) := by
    exact_mod_cast hT
  have hmain : Real.pi / (3 * √3) * Y = (2 * Real.pi / √3 * Y) / 6 := by
    field_simp; ring
  rw [hmain, abs_le] at *
  constructor <;> nlinarith

end Cubic.Counting.TraceZeroSplitCount
