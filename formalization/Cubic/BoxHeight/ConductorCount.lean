import Cubic.BoxHeight.CyclicCubicCharacters
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over the characters `a` as sums over conductors

Supporting identity for `thm:lower` of `box_height_research_note.tex`. The note counts fields by
conductor: `F(s) = ½[(1 + 2·9^{-s}) ∏_{p ≡ 1 (3)} (1 + 2p^{-s}) − 1]`. With the notation of
`CyclicCubicCharacters`, if `S` contains every prime `p ≡ 1 (mod 3)` with `p ≤ Z`, then for
`0 ≤ W ≤ Z`,
`Σ_{a : c_a ≤ W} ψ(c_a) = Σ_{m ≤ W} g(m) ψ(m) + 2 Σ_{m ≤ W/9} g(m) ψ(9m)`,
where `g(m) = 2^{ω(m)}` for squarefree `m` with all prime factors `≡ 1 (mod 3)` and `g(m) = 0`
otherwise: a support `T` carries `2^{|T|}` characters, and `T ↦ ∏ T` matches the supports with
the squarefree `m`.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorCount

open Cubic.BoxHeight.CyclicCubicCharacters

/-- `g(m)`; the same function as `ConductorSum.g`. -/
def gc (m : ℕ) : ℝ :=
  if Squarefree m ∧ ∀ p ∈ m.primeFactors, p % 3 = 1 then 2 ^ m.primeFactors.card else 0

variable {P : SplitSet}

/-- The support of `b : S → ℤ/3`, as a set of primes. -/
def suppN (b : P.S → ZMod 3) : Finset ℕ :=
  (Finset.univ.filter fun p => b p ≠ 0).map (Function.Embedding.subtype _)

theorem suppN_subset (b : P.S → ZMod 3) : suppN b ⊆ P.S := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hx
  exact p.2

theorem mem_suppN (b : P.S → ZMod 3) (p : P.S) : p.1 ∈ suppN b ↔ b p ≠ 0 := by
  simp [suppN]

theorem ne_zero_iff_mem : ∀ x : ZMod 3, x ≠ 0 ↔ x ∈ ({1, 2} : Finset (ZMod 3)) := by decide

/-- `2^{|T|}` functions have support `T`. -/
theorem card_fiber {T : Finset ℕ} (hT : T ⊆ P.S) :
    (Finset.univ.filter fun b : P.S → ZMod 3 => suppN b = T).card = 2 ^ T.card := by
  classical
  have hset : (Finset.univ.filter fun b : P.S → ZMod 3 => suppN b = T) =
      Fintype.piFinset fun p : P.S => if p.1 ∈ T then ({1, 2} : Finset (ZMod 3)) else {0} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl p
      split_ifs with h
      · exact (ne_zero_iff_mem _).mp ((mem_suppN b p).mp h)
      · rw [mem_suppN, not_not] at h; simp [h]
    · intro h
      ext x
      constructor
      · intro hx
        have hxS := suppN_subset b hx
        have := h ⟨x, hxS⟩
        have hb := (mem_suppN b ⟨x, hxS⟩).mp hx
        split_ifs at this with hxT
        · exact hxT
        · simp at this; exact absurd this hb
      · intro hx
        have := h ⟨x, hT hx⟩
        rw [if_pos hx] at this
        exact (mem_suppN b ⟨x, hT hx⟩).mpr ((ne_zero_iff_mem _).mpr this)
  rw [hset, Fintype.card_piFinset]
  have : ∀ p : P.S, (if p.1 ∈ T then ({1, 2} : Finset (ZMod 3)) else {0}).card =
      if p ∈ Finset.univ.filter (fun p : P.S => p.1 ∈ T) then 2 else 1 := by
    intro p
    split_ifs with h h' h' <;> simp_all <;> decide
  rw [Finset.prod_congr rfl fun p _ => this p, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]
  congr 1
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  exact ⟨fun ⟨p, hp, hpx⟩ => hpx ▸ hp, fun hx => ⟨⟨x, hT hx⟩, hx, rfl⟩⟩

/-- The conductor of `b : S → ℤ/3`: the product of its support. -/
def condS (b : P.S → ZMod 3) : ℕ := ∏ p ∈ suppN b, p

theorem primes_of_subset {T : Finset ℕ} (hT : T ⊆ P.S) : ∀ p ∈ T, p.Prime :=
  fun p hp => P.prime p (hT hp)

theorem squarefree_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : Squarefree (∏ p ∈ T, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (f := id) (fun p hp q hq hpq => ?_)
    fun p hp => (hT p hp).prime.squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hT p hp) (hT q hq)).mpr hpq)

/-- The sum over `b : S → ℤ/3` with `c_b ≤ W`, as a sum over `m ≤ W`. -/
theorem sum_condS {Z : ℝ} (hZ : ∀ p : ℕ, p.Prime → p % 3 = 1 → (p : ℝ) ≤ Z → p ∈ P.S)
    {W : ℝ} (hW : W ≤ Z) (ψ : ℕ → ℝ) :
    ∑ b : P.S → ZMod 3, (if (condS b : ℝ) ≤ W then ψ (condS b) else 0) =
      ∑ m ∈ Finset.Icc 1 ⌊W⌋₊, gc m * ψ m := by
  classical
  set F : Finset ℕ → ℝ := fun T => if ((∏ p ∈ T, p : ℕ) : ℝ) ≤ W then ψ (∏ p ∈ T, p) else 0
  have h1 : ∑ b : P.S → ZMod 3, (if (condS b : ℝ) ≤ W then ψ (condS b) else 0) =
      ∑ T ∈ P.S.powerset, (2 : ℝ) ^ T.card * F T := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := P.S.powerset) (g := suppN)
      (fun b _ => Finset.mem_powerset.mpr (suppN_subset b))]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hc : ∀ b ∈ Finset.univ.filter (fun b : P.S → ZMod 3 => suppN b = T),
        (if (condS b : ℝ) ≤ W then ψ (condS b) else 0) = F T := by
      intro b hb
      rw [Finset.mem_filter] at hb
      simp only [F, condS, hb.2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
      card_fiber (Finset.mem_powerset.mp hT)]
    push_cast; ring
  rw [h1]
  have hR : ∑ m ∈ Finset.Icc 1 ⌊W⌋₊, gc m * ψ m =
      ∑ m ∈ (Finset.Icc 1 ⌊W⌋₊).filter (fun m => Squarefree m ∧ ∀ p ∈ m.primeFactors, p % 3 = 1),
        (2 : ℝ) ^ m.primeFactors.card * ψ m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold gc
    split_ifs <;> simp
  have hL : ∑ T ∈ P.S.powerset, (2 : ℝ) ^ T.card * F T =
      ∑ T ∈ P.S.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) ≤ W),
        (2 : ℝ) ^ T.card * ψ (∏ p ∈ T, p) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [F]
    split_ifs <;> simp
  rw [hL, hR]
  refine Finset.sum_nbij' (fun T => ∏ p ∈ T, p) (fun m => m.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have hTp := primes_of_subset hT.1
    have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hTp p hp).pos
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hpos, Nat.le_floor hT.2⟩, squarefree_prod hTp, ?_⟩
    rw [Nat.primeFactors_prod hTp]
    exact fun p hp => P.mod_three p (hT.1 hp)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hW0 : 0 ≤ W := by
      by_contra h
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hm
      omega
    have hmW : (m : ℝ) ≤ W := (Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le hW0)
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun p hp => hZ p (Nat.prime_of_mem_primeFactors hp) (hm.2.2 p hp) ?_, ?_⟩
    · have : p ≤ m := Nat.le_of_dvd hm.1.1 (Nat.dvd_of_mem_primeFactors hp)
      exact (Nat.cast_le.mpr this).trans (hmW.trans hW)
    · rw [Nat.prod_primeFactors_of_squarefree hm.2.1]; exact hmW
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Nat.primeFactors_prod (primes_of_subset hT.1)
  · intro m hm
    simp only [Finset.mem_filter] at hm
    exact Nat.prod_primeFactors_of_squarefree hm.2.1
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    rw [Nat.primeFactors_prod (primes_of_subset hT.1)]

theorem condS_eq (b : P.S → ZMod 3) : condS b = ∏ p : P.S, if b p ≠ 0 then p.1 else 1 := by
  rw [condS, suppN, Finset.prod_map, Finset.prod_filter]
  rfl

theorem cond_eq (a : ι P → ZMod 3) :
    cond P a = (if a none ≠ 0 then 9 else 1) * condS (fun p => a (some p)) := by
  rw [CyclicCubicCharacters.cond, supp, Finset.prod_filter, Fintype.prod_option, condS_eq]
  rfl

theorem univ_zmod_three : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide

/-- The sum over the characters `a` with `c_a ≤ W`. -/
theorem sum_cond {Z : ℝ} (hZ : ∀ p : ℕ, p.Prime → p % 3 = 1 → (p : ℝ) ≤ Z → p ∈ P.S)
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ Z) (ψ : ℕ → ℝ) :
    ∑ a : ι P → ZMod 3, (if (cond P a : ℝ) ≤ W then ψ (cond P a) else 0) =
      ∑ m ∈ Finset.Icc 1 ⌊W⌋₊, gc m * ψ m + 2 * ∑ m ∈ Finset.Icc 1 ⌊W / 9⌋₊, gc m * ψ (9 * m) := by
  classical
  set G : ZMod 3 × (P.S → ZMod 3) → ℝ := fun x =>
    if (((if x.1 ≠ 0 then 9 else 1) * condS x.2 : ℕ) : ℝ) ≤ W then
      ψ ((if x.1 ≠ 0 then 9 else 1) * condS x.2) else 0
  rw [Fintype.sum_equiv Equiv.piOptionEquivProd _ G fun a => by
    simp only [G, cond_eq]; rfl]
  rw [Fintype.sum_prod_type, univ_zmod_three]
  have h9 : ∀ t : ZMod 3, t ≠ 0 → ∑ b : P.S → ZMod 3, G (t, b) =
      ∑ m ∈ Finset.Icc 1 ⌊W / 9⌋₊, gc m * ψ (9 * m) := by
    intro t ht
    rw [← sum_condS hZ (W := W / 9) (by linarith) (fun m => ψ (9 * m))]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [G, if_pos ht]
    push_cast
    have hiff : (9 * (condS b : ℝ) ≤ W) ↔ ((condS b : ℝ) ≤ W / 9) := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 9), mul_comm]
    simp only [hiff]
  have h0 : ∑ b : P.S → ZMod 3, G (0, b) = ∑ m ∈ Finset.Icc 1 ⌊W⌋₊, gc m * ψ m := by
    rw [← sum_condS hZ hW ψ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [G, ne_eq, not_true_eq_false, if_false, one_mul]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h0, h9 1 (by decide), h9 2 (by decide)]
  ring

end Cubic.BoxHeight.ConductorCount
