import Cubic.BoxAsymptotic.TraceWidth
import Mathlib.Topology.Connected.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree

/-!
# Trace lattice counts versus length (`lem:geometry`, part 3)

For a measurable `S ⊆ ℝ` covered by the windows `[r₀ + 3j, r₀ + 3j + 3)`, `j₁ ≤ j ≤ j₂`,
the number of `j` with `r₀ + 3j ∈ S` differs from `|S|/3` by at most the number of windows
meeting the frontier of `S`: a window missing the frontier is, being preconnected, inside
`S` or disjoint from it, and then contributes `0`; any window contributes at most `1`.

For the trace set `E`, the frontier lies in the zeros of `s ∓ H`, `s² - n ∓ 3H` and
`Q(s) - J ∓ 27H`, at most `12` points. Hence each admissible `β` has
`|#{s ≡ r₀ (mod 3) : s ∈ E} - W/3| ≤ 12`: the draft's "differs from its length divided by
`3` by `O(1)`".
-/

noncomputable section

namespace Cubic.BoxAsymptotic.LatticeCount

open MeasureTheory Polynomial Cubic.BoxAsymptotic.TraceWidth

/-- The window `[r₀ + 3j, r₀ + 3j + 3)`. -/
def win (r₀ : ℝ) (j : ℤ) : Set ℝ := Set.Ico (r₀ + 3 * j) (r₀ + 3 * j + 3)

theorem win_disjoint (r₀ : ℝ) {i j : ℤ} (h : i ≠ j) : Disjoint (win r₀ i) (win r₀ j) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h'
    linarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h'
    linarith

theorem subset_or_disjoint {S : Set ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (h : I ∩ frontier S = ∅) : I ⊆ S ∨ Disjoint I S := by
  have hcov : I ⊆ interior S ∪ interior Sᶜ := by
    intro x hx
    by_contra hn
    rw [Set.mem_union, interior_compl, Set.mem_compl_iff, not_or, not_not] at hn
    have : x ∈ frontier S := ⟨hn.2, hn.1⟩
    exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, this⟩
  rcases hI.subset_or_subset isOpen_interior isOpen_interior
      (Set.disjoint_left.mpr fun x h1 h2 => (interior_subset h2 : x ∈ Sᶜ) (interior_subset h1)) hcov with
    h1 | h1
  · exact Or.inl (h1.trans interior_subset)
  · exact Or.inr (Set.disjoint_left.mpr fun x hx hxS => (interior_subset (h1 hx)) hxS)

open scoped Classical in
/-- The window count against the length. -/
theorem window_count {S : Set ℝ} (hS : MeasurableSet S) (r₀ : ℝ) (j₁ j₂ : ℤ)
    (hsub : S ⊆ ⋃ j ∈ Finset.Icc j₁ j₂, win r₀ j) (Z : Finset ℝ) (hZ : frontier S ⊆ Z) :
    |(((Finset.Icc j₁ j₂).filter fun j : ℤ => r₀ + 3 * (j : ℝ) ∈ S).card : ℝ) -
        (volume S).toReal / 3| ≤ Z.card := by
  set J := Finset.Icc j₁ j₂
  have hwin : ∀ j, volume (win r₀ j) = ENNReal.ofReal 3 := fun j => by
    rw [win, Real.volume_Ico]; ring_nf
  have hfin : ∀ j, volume (S ∩ win r₀ j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (by rw [hwin]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have hvol : (volume S).toReal = ∑ j ∈ J, (volume (S ∩ win r₀ j)).toReal := by
    have e : S = ⋃ j ∈ J, S ∩ win r₀ j := by
      ext x; constructor
      · intro hx
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hsub hx)
        exact Set.mem_iUnion₂.mpr ⟨j, hj, hx, hxj⟩
      · intro hx
        obtain ⟨j, -, hxj⟩ := Set.mem_iUnion₂.mp hx
        exact hxj.1
    conv_lhs => rw [e]
    rw [measure_biUnion_finset (fun i _ j _ hij => (win_disjoint r₀ hij).mono
        Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => hS.inter measurableSet_Ico), ENNReal.toReal_sum (fun j _ => hfin j)]
  have hcount : (((J.filter fun j : ℤ => r₀ + 3 * (j : ℝ) ∈ S).card : ℕ) : ℝ) =
      ∑ j ∈ J, (if r₀ + 3 * (j : ℝ) ∈ S then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcount, hvol, Finset.sum_div, ← Finset.sum_sub_distrib]
  -- windows meeting the frontier
  set B := J.filter fun j => (win r₀ j ∩ frontier S).Nonempty
  have hterm : ∀ j ∈ J, |(if r₀ + 3 * (j : ℝ) ∈ S then (1 : ℝ) else 0) -
      (volume (S ∩ win r₀ j)).toReal / 3| ≤ if j ∈ B then 1 else 0 := by
    intro j hj
    have hv : (volume (S ∩ win r₀ j)).toReal ≤ 3 := by
      have := measure_mono (μ := volume) (Set.inter_subset_right : S ∩ win r₀ j ⊆ win r₀ j)
      rw [hwin] at this
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) this
    have hv0 : 0 ≤ (volume (S ∩ win r₀ j)).toReal := ENNReal.toReal_nonneg
    by_cases hB : j ∈ B
    · rw [if_pos hB, abs_le]
      split_ifs <;> constructor <;> linarith
    · rw [if_neg hB]
      have hempty : win r₀ j ∩ frontier S = ∅ := by
        rw [Finset.mem_filter, not_and] at hB
        exact Set.not_nonempty_iff_eq_empty.mp (hB hj)
      have hmem : r₀ + 3 * (j : ℝ) ∈ win r₀ j := ⟨le_rfl, by linarith⟩
      rcases subset_or_disjoint isPreconnected_Ico hempty with h | h
      · rw [if_pos (h hmem), show S ∩ win r₀ j = win r₀ j from Set.inter_eq_right.mpr h, hwin,
          ENNReal.toReal_ofReal (by norm_num)]
        norm_num
      · rw [if_neg (Set.disjoint_left.mp h hmem),
          show S ∩ win r₀ j = ∅ from Set.disjoint_iff_inter_eq_empty.mp h.symm, measure_empty]
        norm_num
  calc |∑ j ∈ J, ((if r₀ + 3 * (j : ℝ) ∈ S then (1 : ℝ) else 0) - (volume (S ∩ win r₀ j)).toReal / 3)|
      ≤ ∑ j ∈ J, |(if r₀ + 3 * (j : ℝ) ∈ S then (1 : ℝ) else 0) -
          (volume (S ∩ win r₀ j)).toReal / 3| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, (if j ∈ B then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
    _ = B.card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext j; simp [B]
    _ ≤ Z.card := by
        have hch : ∀ j ∈ B, ∃ x, x ∈ win r₀ j ∩ frontier S := fun j hj =>
          (Finset.mem_filter.mp hj).2
        choose! f hf using hch
        exact_mod_cast Finset.card_le_card_of_injOn f
          (fun j hj => hZ (hf j hj).2)
          (fun i hi j hj hij => by
            by_contra hne
            exact Set.disjoint_left.mp (win_disjoint r₀ hne) (hf i hi).1 (hij ▸ (hf j hj).1))


theorem roots_finset {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} (hx : p.eval x = 0) : x ∈ p.roots.toFinset := by
  rw [Multiset.mem_toFinset, mem_roots hp]; exact hx

theorem card_roots_le {p : ℝ[X]} {d : ℕ} (hd : p.natDegree ≤ d) : p.roots.toFinset.card ≤ d :=
  (Multiset.toFinset_card_le _).trans ((card_roots' p).trans hd)

/-- The six polynomials whose zeros contain the frontier of `E`. -/
def polys (H n J : ℝ) : Fin 6 → ℝ[X]
  | 0 => X - C H
  | 1 => X + C H
  | 2 => X ^ 2 - C (n + 3 * H)
  | 3 => X ^ 2 - C (n - 3 * H)
  | 4 => C (3 * n) * X - X ^ 3 - C (J + 27 * H)
  | 5 => C (3 * n) * X - X ^ 3 - C (J - 27 * H)

theorem polys_ne_zero (H n J : ℝ) (k : Fin 6) : polys H n J k ≠ 0 := by
  fin_cases k <;> simp only [polys]
  · exact X_sub_C_ne_zero H
  · exact X_add_C_ne_zero H
  · exact (monic_X_pow_sub_C _ two_ne_zero).ne_zero
  · exact (monic_X_pow_sub_C _ two_ne_zero).ne_zero
  · intro h; have := congrArg (fun p => p.coeff 3) h; simp at this
  · intro h; have := congrArg (fun p => p.coeff 3) h; simp at this

def degs : Fin 6 → ℕ
  | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 2 | 4 => 3 | 5 => 3

theorem polys_natDegree (H n J : ℝ) (k : Fin 6) : (polys H n J k).natDegree ≤ degs k := by
  fin_cases k <;> simp only [polys, degs] <;> compute_degree

/-- The zero set `Z`. -/
def Z (H n J : ℝ) : Finset ℝ := Finset.univ.biUnion fun k => (polys H n J k).roots.toFinset

theorem card_Z (H n J : ℝ) : (Z H n J).card ≤ 12 := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k, (polys H n J k).roots.toFinset.card ≤ ∑ k, degs k :=
        Finset.sum_le_sum fun k _ => card_roots_le (polys_natDegree H n J k)
    _ = 12 := by simp [Fin.sum_univ_six, degs]

theorem mem_Z {H n J x : ℝ} (k : Fin 6) (h : (polys H n J k).eval x = 0) : x ∈ Z H n J :=
  Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, roots_finset (polys_ne_zero H n J k) h⟩

theorem frontier_abs_le {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    frontier {x | |f x| ≤ c} ⊆ {x | f x = c ∨ f x = -c} := by
  refine (frontier_le_subset_eq (hf.abs) continuous_const).trans fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx ⊢
  rcases abs_choice (f x) with h | h
  · left; rw [← h, hx]
  · right; rw [← hx, h, neg_neg]

theorem frontier_E (H n θ : ℝ) :
    frontier (E H n θ) ⊆ Z H n (2 * (n * Real.sqrt n) * Real.cos θ) := by
  set J := 2 * (n * Real.sqrt n) * Real.cos θ
  have e : E H n θ = {s | |s| ≤ H} ∩ ({s | |s ^ 2 - n| ≤ 3 * H} ∩
      {s | |Q n s - J| ≤ 27 * H}) := by
    ext s; simp [E, J]
  rw [e]
  intro x hx
  have h1 := frontier_inter_subset _ _ hx
  rcases h1 with ⟨h1, -⟩ | ⟨-, h1⟩
  · rcases frontier_abs_le continuous_id H h1 with h | h
    · exact mem_Z 0 (by
        simp only [polys, eval_sub, eval_X, eval_C]; simp only [id] at h; linarith)
    · exact mem_Z 1 (by
        simp only [polys, eval_add, eval_X, eval_C]; simp only [id] at h; linarith)
  · rcases frontier_inter_subset _ _ h1 with ⟨h2, -⟩ | ⟨-, h2⟩
    · rcases frontier_abs_le (f := fun s => s ^ 2 - n) (by fun_prop) (3 * H) h2 with h | h
      · exact mem_Z 2 (by simp only [polys, eval_sub, eval_pow, eval_X, eval_C]; linarith)
      · exact mem_Z 3 (by simp only [polys, eval_sub, eval_pow, eval_X, eval_C]; linarith)
    · rcases frontier_abs_le (f := fun s => Q n s - J) (by unfold Q; fun_prop) (27 * H) h2 with
        h | h
      · refine mem_Z 4 ?_
        simp only [polys, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
        simp only [Q] at h; linarith
      · refine mem_Z 5 ?_
        simp only [polys, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
        simp only [Q] at h; linarith

theorem measurableSet_E (H n θ : ℝ) : MeasurableSet (E H n θ) := by
  have e : E H n θ = {s | |s| ≤ H} ∩ ({s | |s ^ 2 - n| ≤ 3 * H} ∩
      {s | |Q n s - 2 * (n * Real.sqrt n) * Real.cos θ| ≤ 27 * H}) := by
    ext s; simp [E]
  have : IsClosed (E H n θ) := by
    rw [e]
    refine (isClosed_le continuous_abs continuous_const).inter
      ((isClosed_le (by fun_prop : Continuous fun s : ℝ => |s ^ 2 - n|) continuous_const).inter
        (isClosed_le (by unfold Q; fun_prop :
          Continuous fun s : ℝ => |Q n s - 2 * (n * Real.sqrt n) * Real.cos θ|)
          continuous_const))
  exact this.measurableSet


open scoped Classical in
/-- The traces `s ≡ r₀ (mod 3)` in `E`. -/
def traceSet (H n θ : ℝ) (r₀ : ℤ) : Finset ℤ :=
  (Finset.Icc (-⌈H⌉) ⌈H⌉).filter fun s : ℤ => s ≡ r₀ [ZMOD 3] ∧ (s : ℝ) ∈ E H n θ

open scoped Classical in
/-- **Trace lattice count**: `|#{s ≡ r₀ (mod 3) : s ∈ E} - W/3| ≤ 12`. -/
theorem trace_count (H n θ : ℝ) (r₀ : ℤ) :
    |((traceSet H n θ r₀).card : ℝ) - W H n θ / 3| ≤ 12 := by
  set j₁ := ⌊(-H - r₀) / 3⌋
  set j₂ := ⌈(H - r₀) / 3⌉
  have hcard : (traceSet H n θ r₀).card =
      ((Finset.Icc j₁ j₂).filter fun j : ℤ => (r₀ : ℝ) + 3 * (j : ℝ) ∈ E H n θ).card := by
    symm
    refine Finset.card_bij' (fun j _ => r₀ + 3 * j) (fun s _ => (s - r₀) / 3) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hE := hj.2
      have habs := abs_le.mp hE.1
      rw [traceSet, Finset.mem_filter, Finset.mem_Icc]
      push_cast
      refine ⟨⟨?_, ?_⟩, ?_, hE⟩
      · have : (-(⌈H⌉ : ℝ)) ≤ (r₀ : ℝ) + 3 * j := by linarith [Int.le_ceil H]
        exact_mod_cast this
      · have : (r₀ : ℝ) + 3 * j ≤ (⌈H⌉ : ℝ) := by linarith [Int.le_ceil H]
        exact_mod_cast this
      · exact (Int.modEq_iff_dvd.mpr ⟨j, by ring⟩).symm
    · intro s hs
      rw [traceSet, Finset.mem_filter] at hs
      obtain ⟨-, hmod, hE⟩ := hs
      obtain ⟨k, hk⟩ := (Int.ModEq.dvd hmod.symm)
      have hs' : s = r₀ + 3 * k := by linarith
      have hj : (s - r₀) / 3 = k := by rw [hs']; omega
      dsimp only
      rw [Finset.mem_filter, hj]
      have habs := abs_le.mp hE.1
      have hsk : (s : ℝ) = r₀ + 3 * k := by exact_mod_cast hs'
      refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, by rw [← hsk]; exact hE⟩
      · apply Int.floor_le_iff.mpr
        have : ((-H - r₀) / 3 : ℝ) ≤ k := by rw [div_le_iff₀ (by norm_num)]; linarith
        exact_mod_cast (show ((-H - r₀) / 3 : ℝ) < k + 1 by linarith)
      · apply Int.le_ceil_iff.mpr
        have : (k : ℝ) ≤ (H - r₀) / 3 := by rw [le_div_iff₀ (by norm_num)]; linarith
        exact_mod_cast (show (k : ℝ) - 1 < (H - r₀) / 3 by linarith)
    · intro j _; dsimp only; omega
    · intro s hs
      rw [traceSet, Finset.mem_filter] at hs
      obtain ⟨k, hk⟩ := (Int.ModEq.dvd hs.2.1.symm)
      dsimp only; omega
  rw [hcard]
  have hcov : E H n θ ⊆ ⋃ j ∈ Finset.Icc j₁ j₂, win r₀ j := by
    intro x hx
    have habs := abs_le.mp hx.1
    set j := ⌊(x - r₀) / 3⌋
    refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_Icc.mpr ⟨Int.floor_mono (by linarith), ?_⟩, ?_⟩
    · have h1 := Int.floor_le ((x - r₀) / 3)
      have h2 := Int.le_ceil ((H - r₀) / 3)
      have : (j : ℝ) ≤ j₂ := by
        have : (x - r₀) / 3 ≤ (H - r₀) / 3 := by linarith
        linarith
      exact_mod_cast this
    · have h1 := Int.floor_le ((x - r₀) / 3)
      have h2 := Int.lt_floor_add_one ((x - r₀) / 3)
      constructor <;> linarith
  have := window_count (measurableSet_E H n θ) r₀ j₁ j₂ hcov _ (frontier_E H n θ)
  exact this.trans (by exact_mod_cast card_Z H n _)

end Cubic.BoxAsymptotic.LatticeCount
