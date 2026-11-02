import Cubic.Counting.EisensteinNormCount
import Cubic.Counting.GeneralMonicData

/-!
# The lattice points behind `lemma:traceZeroCoefficients`

For `K = N³`, let `T` be the points `(a, b)` with `a² - ab + b² = K` and `3 ∣ b`, i.e. the
elements `a + bζ` of norm `N³` whose `ζ`-coefficient is divisible by `3`.

* Multiplication by `ζ` sends `(a, b)` to `(-b, a - b)`, so the `ζ`-coefficients of
  `α, ζα, ζ²α` are `b, a - b, -a`. If `3 ∤ K`, exactly one is divisible by `3`, so `T` is a
  third of all points; if `9 ∣ K`, then `3 ∣ a` and `3 ∣ b` for every point.
* `(a, b) ↦ (c, δ) = (b/3, 2a - b)` identifies `T` with the solutions of `δ² + 27c² = 4N³`.
  Such a solution with `δ > 0` comes in a pair `±δ`, and `δ = 0` exactly when
  `N = 3u²`, `c = ±2u³`.
-/

noncomputable section

namespace Cubic.Counting.TraceZeroLattice

open Cubic.Counting.EisensteinNormCount Cubic.Counting.GeneralMonicData

/-- Multiplication by `ζ` in coordinates. -/
def rot (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1 - p.2)

theorem rot_rot_rot (p : ℤ × ℤ) : rot (rot (rot p)) = p := by
  ext <;> simp only [rot] <;> ring

theorem rot_injective : Function.Injective rot := fun p q h => by
  rw [← rot_rot_rot p, ← rot_rot_rot q, h]

theorem rot_mem {K : ℤ} {p : ℤ × ℤ} (hp : p ∈ normSet K) : rot p ∈ normSet K := by
  simp only [normSet, Set.mem_setOf_eq, rot] at hp ⊢; rw [← hp]; ring

/-- The points with `3 ∣ b`. -/
def slice (K : ℤ) : Set (ℤ × ℤ) := {p | p ∈ normSet K ∧ 3 ∣ p.2}

theorem slice_finite (K : ℤ) : (slice K).Finite := (normSet_finite K).subset fun _ h => h.1

theorem dvd_three_iff (n : ℤ) : 3 ∣ n ↔ (n : ZMod 3) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).symm

/-- If `3 ∤ a² - ab + b²`, exactly one of `b, a - b, a` is divisible by `3`. -/
theorem exactly_one {a b : ℤ} (h : ¬ 3 ∣ a ^ 2 - a * b + b ^ 2) :
    (3 ∣ b ∨ 3 ∣ a - b ∨ 3 ∣ a) ∧ ¬ (3 ∣ b ∧ 3 ∣ a - b) ∧ ¬ (3 ∣ b ∧ 3 ∣ a) ∧
      ¬ (3 ∣ a - b ∧ 3 ∣ a) := by
  have key : ∀ x y : ZMod 3, x ^ 2 - x * y + y ^ 2 ≠ 0 →
      (y = 0 ∨ x - y = 0 ∨ x = 0) ∧ ¬ (y = 0 ∧ x - y = 0) ∧ ¬ (y = 0 ∧ x = 0) ∧
        ¬ (x - y = 0 ∧ x = 0) := by decide
  rw [dvd_three_iff] at h
  push_cast at h
  simp only [dvd_three_iff]
  push_cast
  exact key _ _ h

/-- If `9 ∣ a² - ab + b²`, then `3 ∣ a` and `3 ∣ b`. -/
theorem three_dvd_of_nine_dvd {a b : ℤ} (h : 9 ∣ a ^ 2 - a * b + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  have key : ∀ x y : ZMod 9, x ^ 2 - x * y + y ^ 2 = 0 →
      ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) x = 0 ∧
        ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) y = 0 := by decide
  have h' : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr (by exact_mod_cast h)
  push_cast at h'
  have := key _ _ h'
  simp only [map_intCast] at this
  exact ⟨(dvd_three_iff a).mpr this.1, (dvd_three_iff b).mpr this.2⟩

/-- If `3 ∤ K`, the slice is a third of all points. -/
theorem three_mul_ncard_slice {K : ℤ} (hK : ¬ 3 ∣ K) :
    3 * (slice K).ncard = (normSet K).ncard := by
  let A : Set (ℤ × ℤ) := {p | p ∈ normSet K ∧ 3 ∣ p.1 - p.2}
  let B : Set (ℤ × ℤ) := {p | p ∈ normSet K ∧ 3 ∣ p.1}
  have hfin := normSet_finite K
  have hone : ∀ p ∈ normSet K, _ := fun p (hp : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K) =>
    exactly_one (a := p.1) (b := p.2) (by rw [hp]; exact hK)
  have hA : rot '' A = slice K := by
    ext t
    constructor
    · rintro ⟨p, ⟨hp, hd⟩, rfl⟩; exact ⟨rot_mem hp, by simpa [rot] using hd⟩
    · rintro ⟨ht, hd⟩
      refine ⟨rot (rot t), ⟨rot_mem (rot_mem ht), ?_⟩, rot_rot_rot t⟩
      simp only [rot]
      convert hd using 1; ring
  have hB : (rot ∘ rot) '' B = slice K := by
    ext t
    constructor
    · rintro ⟨p, ⟨hp, hd⟩, rfl⟩
      refine ⟨rot_mem (rot_mem hp), ?_⟩
      simp only [Function.comp, rot]
      convert hd.neg_right using 1; ring
    · rintro ⟨ht, hd⟩
      refine ⟨rot t, ⟨rot_mem ht, ?_⟩, rot_rot_rot t⟩
      simpa [rot] using hd
  have hcA : A.ncard = (slice K).ncard := by
    rw [← hA, Set.ncard_image_of_injective _ rot_injective]
  have hcB : B.ncard = (slice K).ncard := by
    rw [← hB, Set.ncard_image_of_injective _ (rot_injective.comp rot_injective)]
  have hunion : normSet K = slice K ∪ A ∪ B := by
    ext p
    constructor
    · intro hp
      rcases (hone p hp).1 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inl (Or.inr ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  have hd1 : Disjoint (slice K) A := Set.disjoint_left.mpr fun p h1 h2 =>
    (hone p h1.1).2.1 ⟨h1.2, h2.2⟩
  have hd2 : Disjoint (slice K ∪ A) B := Set.disjoint_left.mpr fun p h1 h2 => by
    rcases h1 with h1 | h1
    · exact (hone p h1.1).2.2.1 ⟨h1.2, h2.2⟩
    · exact (hone p h1.1).2.2.2 ⟨h1.2, h2.2⟩
  rw [hunion, Set.ncard_union_eq hd2 ((slice_finite K).union (hfin.subset fun _ h => h.1))
    (hfin.subset fun _ h => h.1), Set.ncard_union_eq hd1 (slice_finite K)
    (hfin.subset fun _ h => h.1), hcA, hcB]
  ring

/-- If `9 ∣ K`, every point lies in the slice. -/
theorem slice_eq_of_nine_dvd {K : ℤ} (hK : 9 ∣ K) : slice K = normSet K := by
  ext p
  refine ⟨fun h => h.1, fun hp => ⟨hp, ?_⟩⟩
  have hp' : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K := hp
  exact (three_dvd_of_nine_dvd (hp' ▸ hK)).2

/-! ### The correspondence with `δ² + 27c² = 4N³` -/

/-- Solutions `(c, δ)` of `δ² + 27c² = 4N³`. -/
def sol (N : ℤ) : Set (ℤ × ℤ) := {q | q.2 ^ 2 + 27 * q.1 ^ 2 = 4 * N ^ 3}

theorem parity {c δ K : ℤ} (h : δ ^ 2 + 27 * c ^ 2 = 4 * K) : 2 ∣ δ + 3 * c := by
  have h2 : (2 : ℤ) ∣ δ ^ 2 + 27 * c ^ 2 := ⟨2 * K, by rw [h]; ring⟩
  obtain ⟨z, hz⟩ := h2
  rcases Int.even_or_odd δ with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases Int.even_or_odd c with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨x + 3 * y, by ring⟩
  · have e : 2 * (2 * x ^ 2 + 54 * y ^ 2 + 54 * y + 13) + 1 = 2 * z := by linear_combination hz
    generalize 2 * x ^ 2 + 54 * y ^ 2 + 54 * y + 13 = t at e; omega
  · have e : 2 * (2 * x ^ 2 + 2 * x + 54 * y ^ 2) + 1 = 2 * z := by linear_combination hz
    generalize 2 * x ^ 2 + 2 * x + 54 * y ^ 2 = t at e; omega
  · exact ⟨x + 3 * y + 2, by ring⟩

theorem slice_to_sol {N : ℤ} {p : ℤ × ℤ} (hp : p ∈ slice (N ^ 3)) :
    (p.2 / 3, 2 * p.1 - p.2) ∈ sol N := by
  obtain ⟨a, b⟩ := p
  obtain ⟨h, c, hc⟩ := hp
  have h' : a ^ 2 - a * b + b ^ 2 = N ^ 3 := h
  simp only at hc
  show (2 * a - b) ^ 2 + 27 * (b / 3) ^ 2 = 4 * N ^ 3
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num), ← h', hc]; ring

theorem sol_to_slice {N : ℤ} {q : ℤ × ℤ} (hq : q ∈ sol N) :
    ((q.2 + 3 * q.1) / 2, 3 * q.1) ∈ slice (N ^ 3) := by
  obtain ⟨c, δ⟩ := q
  have h : δ ^ 2 + 27 * c ^ 2 = 4 * N ^ 3 := hq
  obtain ⟨k, hk⟩ := parity h
  refine ⟨?_, ⟨c, rfl⟩⟩
  show ((δ + 3 * c) / 2) ^ 2 - (δ + 3 * c) / 2 * (3 * c) + (3 * c) ^ 2 = N ^ 3
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  have h4 : 4 * (k ^ 2 - k * (3 * c) + (3 * c) ^ 2) = 4 * N ^ 3 := by
    rw [← h, show δ = 2 * k - 3 * c by linarith]; ring
  exact mul_left_cancel₀ (by norm_num) h4

/-- `(a, b) ↦ (b/3, 2a - b)`, with inverse `(c, δ) ↦ ((δ + 3c)/2, 3c)`. -/
def sliceEquiv (N : ℤ) : slice (N ^ 3) ≃ sol N where
  toFun p := ⟨_, slice_to_sol p.2⟩
  invFun q := ⟨_, sol_to_slice q.2⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, h, c, hc⟩ := p
    simp only at hc
    subst hc
    apply Subtype.ext
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]
    rw [show 2 * a - 3 * c + 3 * c = 2 * a by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  right_inv q := by
    obtain ⟨⟨c, δ⟩, h⟩ := q
    obtain ⟨k, hk⟩ := parity h
    apply Subtype.ext
    simp only [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0),
      Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]
    ext
    · rfl
    · show 2 * k - 3 * c = δ; linarith

/-- Solutions with `δ ≥ 0` correspond to the `c` counted by `r(N)`. -/
def nonnegEquiv (N : ℤ) : {q : ℤ × ℤ // q ∈ sol N ∧ 0 ≤ q.2} ≃ squareSet N where
  toFun q := ⟨q.1.1, ⟨q.1.2, by
    have h : q.1.2 ^ 2 + 27 * q.1.1 ^ 2 = 4 * N ^ 3 := q.2.1
    linear_combination -h⟩⟩
  invFun c := ⟨(c.1, |c.2.choose|), by
    have h := c.2.choose_spec
    refine ⟨?_, abs_nonneg _⟩
    show |c.2.choose| ^ 2 + 27 * c.1 ^ 2 = 4 * N ^ 3
    rw [sq_abs]; linear_combination -h⟩
  left_inv q := by
    obtain ⟨⟨c, δ⟩, h, hδ⟩ := q
    have h' : δ ^ 2 + 27 * c ^ 2 = 4 * N ^ 3 := h
    apply Subtype.ext
    ext
    · rfl
    · show |_| = δ
      have hsq : IsSquare (4 * N ^ 3 - 27 * c ^ 2) := ⟨δ, by linear_combination -h'⟩
      have hr := hsq.choose_spec
      have habs : |hsq.choose| = |δ| := sq_eq_sq_iff_abs_eq_abs _ _ |>.mp (by nlinarith)
      rw [abs_of_nonneg hδ] at habs
      exact habs
  right_inv c := rfl

theorem sol_finite (N : ℤ) : (sol N).Finite := by
  haveI := (slice_finite (N ^ 3)).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (sliceEquiv N))

/-- `δ = 0` occurs exactly when `N = 3u²`, and then `c = ±2u³`. -/
theorem exists_of_zero {N c : ℤ} (hN : 1 ≤ N) (h : 27 * c ^ 2 = 4 * N ^ 3) :
    ∃ u : ℤ, 0 < u ∧ N = 3 * u ^ 2 := by
  have h2 : (2 : ℤ) ∣ c := by
    have : (2 : ℤ) ∣ 27 * c ^ 2 := ⟨2 * N ^ 3, by rw [h]; ring⟩
    exact Int.prime_two.dvd_of_dvd_pow
      ((Int.prime_two.dvd_or_dvd this).resolve_left (by norm_num))
  obtain ⟨c', rfl⟩ := h2
  have h' : 27 * c' ^ 2 = N ^ 3 := by linarith
  have h3 : (3 : ℤ) ∣ N := Int.prime_three.dvd_of_dvd_pow (n := 3) ⟨9 * c' ^ 2, by rw [← h']; ring⟩
  obtain ⟨n, rfl⟩ := h3
  have hn : c' ^ 2 = n ^ 3 := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; omega
  have hdvd : n ∣ c' := (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    ⟨n, by rw [hn]; ring⟩
  obtain ⟨k, rfl⟩ := hdvd
  have hk : n = k ^ 2 := by
    have : n ^ 2 * (k ^ 2 - n) = 0 := by linear_combination hn
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h0) hn0
    · linarith
  refine ⟨|k|, abs_pos.mpr ?_, by rw [hk, sq_abs]⟩
  rintro rfl; simp at hk; exact hn0 hk

open scoped Classical in
theorem ncard_zero {N : ℤ} (hN : 1 ≤ N) :
    {q | q ∈ sol N ∧ q.2 = 0}.ncard = if ∃ u : ℤ, 0 < u ∧ N = 3 * u ^ 2 then 2 else 0 := by
  split_ifs with hu
  · obtain ⟨u, hu0, rfl⟩ := hu
    have hset : {q | q ∈ sol (3 * u ^ 2) ∧ q.2 = 0} = {(2 * u ^ 3, 0), (-(2 * u ^ 3), 0)} := by
      ext ⟨c, δ⟩
      simp only [sol, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨h, rfl⟩
        have hc : c ^ 2 = (2 * u ^ 3) ^ 2 := by linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hc | hc
        · exact Or.inl ⟨hc, rfl⟩
        · exact Or.inr ⟨hc, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> refine ⟨by ring, rfl⟩
    rw [hset, Set.ncard_pair]
    intro h
    simp only [Prod.mk.injEq, and_true] at h
    have : u ^ 3 = 0 := by linarith
    exact hu0.ne' (pow_eq_zero_iff (by norm_num) |>.mp this)
  · rw [Set.ncard_eq_zero ((sol_finite N).subset fun _ h => h.1)]
    ext ⟨c, δ⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h hδ
    have h' : δ ^ 2 + 27 * c ^ 2 = 4 * N ^ 3 := h
    subst hδ
    exact hu (exists_of_zero hN (by linarith))

/-- `#{δ² + 27c² = 4N³} + #{δ = 0} = 2 r(N)`. -/
theorem ncard_sol_add (N : ℤ) :
    (sol N).ncard + {q | q ∈ sol N ∧ q.2 = 0}.ncard = 2 * r N := by
  let P : Set (ℤ × ℤ) := {q | q ∈ sol N ∧ 0 ≤ q.2}
  let Q : Set (ℤ × ℤ) := {q | q ∈ sol N ∧ q.2 ≤ 0}
  have hfin := sol_finite N
  have hPQ : P ∪ Q = sol N := by
    ext q; constructor
    · rintro (h | h) <;> exact h.1
    · intro h; rcases le_total 0 q.2 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hPQ' : P ∩ Q = {q | q ∈ sol N ∧ q.2 = 0} := by
    ext q; constructor
    · rintro ⟨⟨h, h1⟩, -, h2⟩; exact ⟨h, le_antisymm h2 h1⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, h'.ge⟩, h, h'.le⟩
  have hneg : (fun q : ℤ × ℤ => (q.1, -q.2)) '' P = Q := by
    ext ⟨c, δ⟩; constructor
    · rintro ⟨⟨c', δ'⟩, ⟨h, h'⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨?_, by simp only; linarith⟩
      have h1 : δ' ^ 2 + 27 * c' ^ 2 = 4 * N ^ 3 := h
      show (-δ') ^ 2 + 27 * c' ^ 2 = 4 * N ^ 3; rw [neg_sq]; exact h1
    · rintro ⟨h, h'⟩
      have h1 : δ ^ 2 + 27 * c ^ 2 = 4 * N ^ 3 := h
      refine ⟨(c, -δ), ⟨?_, by simp only; linarith⟩, by simp⟩
      show (-δ) ^ 2 + 27 * c ^ 2 = 4 * N ^ 3; rw [neg_sq]; exact h1
  have hinj : Function.Injective (fun q : ℤ × ℤ => (q.1, -q.2)) := by
    intro p q h; simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2
  have hQ : Q.ncard = P.ncard := by rw [← hneg, Set.ncard_image_of_injective _ hinj]
  have hP : P.ncard = r N := by
    rw [r, ← Nat.card_congr (nonnegEquiv N)]; exact (Nat.card_coe_set_eq P).symm
  rw [← hPQ', show (sol N).ncard = (P ∪ Q).ncard by rw [hPQ], Set.ncard_union_add_ncard_inter _ _ (hfin.subset fun _ h => h.1)
    (hfin.subset fun _ h => h.1), hQ, hP]
  ring

theorem squareSet_finite (N : ℤ) : (squareSet N).Finite := by
  have hP : Set.Finite {q : ℤ × ℤ | q ∈ sol N ∧ 0 ≤ q.2} := (sol_finite N).subset fun _ h => h.1
  haveI : Finite {q : ℤ × ℤ // q ∈ sol N ∧ 0 ≤ q.2} := hP.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (nonnegEquiv N))

end Cubic.Counting.TraceZeroLattice
