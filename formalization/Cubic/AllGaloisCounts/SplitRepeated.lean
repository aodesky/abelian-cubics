import Cubic.AllGaloisCounts.SplitOrbits

/-! Repeated-root orderings account for only `O(H²)` in the six-to-one
comparison. Burnside's identity records the same exceptional multiplicities. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SplitRepeated
open CountData HeightBox SplitOrbits

def repeated (H : ℝ) : Set (Triples H) :=
  {v | v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2}

theorem two_equal_of_fixed {H : ℝ} {σ : Equiv.Perm (Fin 3)} (hσ : σ ≠ 1)
    {v : Triples H} (hv : σ • v = v) : v ∈ repeated H := by
  obtain ⟨i, hi⟩ : ∃ i, σ⁻¹ i ≠ i := by
    by_contra h
    push_neg at h
    exact hσ (inv_eq_one.mp (Equiv.ext h))
  have he : v.1 (σ⁻¹ i) = v.1 i := by
    rw [← smul_apply]
    exact congrFun (congrArg Subtype.val hv) i
  change v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2
  generalize σ⁻¹ i = j at hi he
  fin_cases i <;> fin_cases j <;> simp at hi he ⊢ <;> tauto

theorem repeated_card_le (H : ℝ) :
    (repeated H).ncard ≤ ((⌊2 * H⌋ + 1 - -⌊2 * H⌋).toNat) ^ 2 * 3 := by
  classical
  set B := ⌊2 * H⌋
  let φ : Triples H → (ℤ × ℤ) × Fin 3 := fun v =>
    if v.1 0 = v.1 1 then ((v.1 0, v.1 2), 0)
    else if v.1 0 = v.1 2 then ((v.1 0, v.1 1), 1)
    else ((v.1 1, v.1 0), 2)
  let S : Finset ((ℤ × ℤ) × Fin 3) :=
    (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B) ×ˢ Finset.univ
  have hbound : ∀ (v : Triples H) (i : Fin 3), -B ≤ v.1 i ∧ v.1 i ≤ B := by
    intro v i
    exact (int_abs_iff _ _).mp (coordinate_bound v i)
  have hmaps : Set.MapsTo φ (repeated H) (S : Set ((ℤ × ℤ) × Fin 3)) := by
    intro v _
    simp only [φ, S, Finset.coe_product, Finset.coe_Icc, Finset.coe_univ, Set.mem_prod,
      Set.mem_Icc, Set.mem_univ, and_true]
    split_ifs <;> exact ⟨hbound _ _, hbound _ _⟩
  have hinj : Set.InjOn φ (repeated H) := by
    intro v hv w hw h
    change v.1 0 = v.1 1 ∨ v.1 0 = v.1 2 ∨ v.1 1 = v.1 2 at hv
    change w.1 0 = w.1 1 ∨ w.1 0 = w.1 2 ∨ w.1 1 = w.1 2 at hw
    apply Subtype.ext
    funext k
    simp only [φ] at h
    split_ifs at h <;> simp [Prod.ext_iff] at h <;> fin_cases k <;> simp <;> omega
  calc _ ≤ (S : Set ((ℤ × ℤ) × Fin 3)).ncard :=
      Set.ncard_le_ncard_of_injOn φ hmaps hinj S.finite_toSet
    _ = _ := by
      simp only [S, Set.ncard_coe_finset, Finset.card_product, Int.card_Icc,
        Finset.card_univ, Fintype.card_fin, sq]

theorem repeated_bound {H : ℝ} (hH : 1 ≤ H) : ((repeated H).ncard : ℝ) ≤ 75 * H ^ 2 := by
  have h0 : 0 ≤ ⌊2 * H⌋ := Int.floor_nonneg.mpr (by linarith)
  have he : (((⌊2 * H⌋ + 1 - -⌊2 * H⌋).toNat : ℕ) : ℝ) = 2 * (⌊2 * H⌋ : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  have hb := repeated_card_le H
  have hb' : ((repeated H).ncard : ℝ) ≤
      (((⌊2 * H⌋ + 1 - -⌊2 * H⌋).toNat : ℕ) : ℝ) ^ 2 * 3 := by exact_mod_cast hb
  rw [he] at hb'
  have hh : 0 ≤ (⌊2 * H⌋ : ℝ) := by exact_mod_cast h0
  have hle : 2 * (⌊2 * H⌋ : ℝ) + 1 ≤ 5 * H := by linarith [Int.floor_le (2 * H)]
  nlinarith [sq_le_sq₀ (by positivity : 0 ≤ 2 * (⌊2 * H⌋ : ℝ) + 1)
    (by linarith : 0 ≤ 5 * H) |>.mpr hle]

theorem burnside_bounds (H : ℝ) :
    (Triples H).ncard ≤ 6 * N .trivial H ∧
      6 * N .trivial H ≤ (Triples H).ncard + 5 * (repeated H).ncard := by
  classical
  haveI : Fintype (Triples H) := (triples_finite H).fintype
  haveI : ∀ σ : Equiv.Perm (Fin 3), Fintype (MulAction.fixedBy (Triples H) σ) :=
    fun _ => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples H)) :=
    Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin 3)) (Triples H)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card, card_orbits,
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ 1)] at hB
  have h1 : Fintype.card (MulAction.fixedBy (Triples H) (1 : Equiv.Perm (Fin 3))) =
      (Triples H).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun v => MulAction.mem_fixedBy.mpr (one_smul _ v))), Nat.card_coe_set_eq]
  have hfix : ∀ σ ∈ Finset.univ \ {(1 : Equiv.Perm (Fin 3))},
      Fintype.card (MulAction.fixedBy (Triples H) σ) ≤ (repeated H).ncard := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := by simpa using hσ
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun v hv => two_equal_of_fixed hσ1 hv) (Set.toFinite _)
  have hsum := Finset.sum_le_card_nsmul _ _ _ hfix
  have hcard : (Finset.univ \ {(1 : Equiv.Perm (Fin 3))}).card = 5 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_perm]
    simp [Nat.factorial]
  rw [hcard, smul_eq_mul] at hsum
  rw [h1, show Nat.factorial 3 = 6 from rfl] at hB
  constructor <;> omega

theorem six_count_error {H : ℝ} (hH : 1 ≤ H) :
    |6 * (N .trivial H : ℝ) - (Nat.card (Triples H) : ℝ)| ≤ 375 * H ^ 2 := by
  obtain ⟨hlo, hhi⟩ := burnside_bounds H
  have hlo' : ((Triples H).ncard : ℝ) ≤ 6 * N .trivial H := by exact_mod_cast hlo
  have hhi' : 6 * (N .trivial H : ℝ) ≤ (Triples H).ncard + 5 * (repeated H).ncard := by
    exact_mod_cast hhi
  rw [Nat.card_coe_set_eq, abs_of_nonneg (sub_nonneg.mpr hlo')]
  linarith [repeated_bound hH]

end Cubic.AllGaloisCounts.SplitRepeated
