import Cubic.Counting.CubicDiscriminantSquare
import Cubic.Counting.TraceZeroLattice
import Cubic.Counting.GeneralHeightReduction

/-!
# Trace-zero cubics with square discriminant

Supporting facts for `prop:traceZeroAsymptotic`. The discriminant of `t³ - Nt + c` is
`4N³ - 27c²`, so `r(N)` counts the `c` for which it is a square. For `N ≥ 1` this happens
exactly when the cubic has Galois group `C₃` or splits over `ℚ`, and not both: "a reducible
monic cubic with square discriminant splits completely". When the discriminant vanishes,
`N = 3u²` and `c = ±2u³`, and the cubic is `(t ∓ u)²(t ± 2u)`. Hence
`A₀(X) + #{split t³ - Nt + c : 1 ≤ N ≤ X} = Σ_{1 ≤ N ≤ X} r(N)`.
-/

noncomputable section

namespace Cubic.Counting.TraceZeroSplitting

open Polynomial Cubic.Counting.GeneralMonicData Cubic.Counting.CubicDiscriminantSquare
open Cubic.Counting.TraceZeroLattice Cubic.Counting.GeneralHeightReduction
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- `t³ - Nt + c` as a rational cubic. -/
def cubicData (N c : ℤ) : _root_.Cubic ℚ := ⟨1, 0, -N, c⟩

theorem toPoly_cubicData (N c : ℤ) :
    (cubicData N c).toPoly = (monicCubic 0 (-N) c).map (Int.castRingHom ℚ) := by
  simp [cubicData, _root_.Cubic.toPoly, monicCubic]

theorem discr_cubicData (N c : ℤ) :
    (cubicData N c).discr = ((4 * N ^ 3 - 27 * c ^ 2 : ℤ) : ℚ) := by
  simp [cubicData, _root_.Cubic.discr]; ring

/-- The split case of a vanishing discriminant: `(t ∓ u)²(t ± 2u)`. -/
theorem splits_of_discr_zero {N c : ℤ} (hN : 1 ≤ N) (h : 4 * N ^ 3 - 27 * c ^ 2 = 0) :
    ((monicCubic 0 (-N) c).map (Int.castRingHom ℚ)).Splits := by
  obtain ⟨u, -, rfl⟩ := exists_of_zero hN (by linarith)
  have hc : c ^ 2 = (2 * u ^ 3) ^ 2 := by linarith
  have hfac : ∀ v : ℤ, c = 2 * v ^ 3 → u ^ 2 = v ^ 2 →
      (monicCubic 0 (-(3 * u ^ 2)) c).map (Int.castRingHom ℚ) =
        (X - C (v : ℚ)) ^ 2 * (X - C (-2 * v : ℚ)) := by
    rintro v rfl huv
    have huv' : ((u : ℚ)) ^ 2 = (v : ℚ) ^ 2 := by exact_mod_cast huv
    simp only [monicCubic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    simp only [eq_intCast]
    push_cast
    rw [huv']
    simp only [map_mul, map_pow, map_neg, map_ofNat, map_zero, zero_mul, add_zero]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with h' | h'
  · rw [hfac u h' rfl]
    exact ((Splits.X_sub_C _).pow 2).mul (Splits.X_sub_C _)
  · rw [hfac (-u) (by rw [h']; ring) (by ring)]
    exact ((Splits.X_sub_C _).pow 2).mul (Splits.X_sub_C _)

/-- For `N ≥ 1`, `4N³ - 27c²` is a square iff `t³ - Nt + c` is cyclic or split. -/
theorem isSquare_iff {N c : ℤ} (hN : 1 ≤ N) :
    IsSquare (4 * N ^ 3 - 27 * c ^ 2) ↔
      HasCyclicCubicGaloisGroup ((monicCubic 0 (-N) c).map (Int.castRingHom ℚ)) ∨
        ((monicCubic 0 (-N) c).map (Int.castRingHom ℚ)).Splits := by
  have ha : (cubicData N c).a = 1 := rfl
  constructor
  · rintro ⟨s, hs⟩
    by_cases hs0 : s = 0
    · subst hs0
      exact Or.inr (splits_of_discr_zero hN (by simpa using hs))
    rw [← toPoly_cubicData]
    refine cyclic_or_splits_of_discr ha (d := s) ?_ (by exact_mod_cast hs0)
    rw [discr_cubicData, hs]; push_cast; ring
  · intro h
    rw [← toPoly_cubicData] at h
    obtain ⟨d, hd⟩ := h.elim (discr_square_of_cyclic ha) (discr_square_of_splits ha)
    rw [discr_cubicData] at hd
    exact Rat.isSquare_intCast_iff.mp ⟨d, by rw [hd]; ring⟩

theorem not_cyclic_and_splits (f : ℚ[X]) (hc : HasCyclicCubicGaloisGroup f) (hs : f.Splits) :
    False := by
  obtain ⟨e⟩ := hc
  letI := Gal.uniqueGalOfSplits _ hs
  have := Nat.card_congr e.toEquiv
  simp at this

/-! ### The decomposition of `Σ r(N)` -/

/-- Split trace-zero cubics `t³ - Nt + c` with `1 ≤ N ≤ X`. -/
def splitSet (X : ℝ) : Set ℤ[X] :=
  {f | ∃ N c : ℤ, f = monicCubic 0 (-N) c ∧ 1 ≤ N ∧ (N : ℝ) ≤ X ∧
    (f.map (Int.castRingHom ℚ)).Splits}

/-- `(N, c) ↦ t³ - Nt + c`. -/
def toCubic (q : ℤ × ℤ) : ℤ[X] := monicCubic 0 (-q.1) q.2

theorem toCubic_injective : Function.Injective toCubic := by
  intro p q h
  have h1 := congrArg (fun f => f.coeff 1) h
  have h0 := congrArg (fun f => f.coeff 0) h
  simp only [toCubic, monicCubic_coeff_one, monicCubic_coeff_zero, neg_inj] at h1 h0
  exact Prod.ext h1 h0

/-- Pairs `(N, c)` with `1 ≤ N ≤ X` and square discriminant. -/
def pairs (X : ℝ) : Set (ℤ × ℤ) :=
  {q | 1 ≤ q.1 ∧ (q.1 : ℝ) ≤ X ∧ IsSquare (4 * q.1 ^ 3 - 27 * q.2 ^ 2)}

theorem pairs_eq (X : ℝ) :
    pairs X = ↑((Finset.Icc 1 ⌊X⌋).biUnion fun N =>
      (squareSet_finite N).toFinset.map ⟨fun c => (N, c), fun _ _ h => (Prod.mk.inj h).2⟩) := by
  ext ⟨N, c⟩
  simp only [pairs, Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_Icc, Set.mem_iUnion,
    Set.mem_Icc, Finset.coe_map, Function.Embedding.coeFn_mk, Set.Finite.coe_toFinset,
    Set.mem_image, Prod.mk.injEq, exists_prop]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨N, ⟨h1, Int.le_floor.mpr (by exact_mod_cast h2)⟩, c, h3, rfl, rfl⟩
  · rintro ⟨N', ⟨h1, h2⟩, c', h3, rfl, rfl⟩
    exact ⟨h1, by exact_mod_cast Int.le_floor.mp h2, h3⟩

theorem ncard_pairs (X : ℝ) : (pairs X).ncard = ∑ N ∈ Finset.Icc 1 ⌊X⌋, r N := by
  rw [pairs_eq, Set.ncard_coe_finset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.card_map, ← Set.ncard_eq_toFinset_card _ (squareSet_finite N), r,
      Nat.card_coe_set_eq]
  · intro N _ N' _ hNN'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q h h'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h h'
    obtain ⟨_, _, rfl⟩ := h
    obtain ⟨_, _, h⟩ := h'
    exact hNN' (Prod.mk.inj h).1.symm

theorem traceZeroSet_eq (X : ℝ) :
    traceZeroSet X = toCubic '' {q | q ∈ pairs X ∧
      HasCyclicCubicGaloisGroup ((toCubic q).map (Int.castRingHom ℚ))} := by
  ext f
  constructor
  · rintro ⟨N, c, rfl, h1, h2, hc⟩
    exact ⟨(N, c), ⟨⟨h1, h2, (isSquare_iff h1).mpr (Or.inl hc)⟩, hc⟩, rfl⟩
  · rintro ⟨⟨N, c⟩, ⟨⟨h1, h2, -⟩, hc⟩, rfl⟩
    exact ⟨N, c, rfl, h1, h2, hc⟩

theorem splitSet_eq (X : ℝ) :
    splitSet X = toCubic '' {q | q ∈ pairs X ∧ ((toCubic q).map (Int.castRingHom ℚ)).Splits} := by
  ext f
  constructor
  · rintro ⟨N, c, rfl, h1, h2, hs⟩
    exact ⟨(N, c), ⟨⟨h1, h2, (isSquare_iff h1).mpr (Or.inr hs)⟩, hs⟩, rfl⟩
  · rintro ⟨⟨N, c⟩, ⟨⟨h1, h2, -⟩, hs⟩, rfl⟩
    exact ⟨N, c, rfl, h1, h2, hs⟩

theorem pairs_finite (X : ℝ) : (pairs X).Finite := by rw [pairs_eq]; exact Finset.finite_toSet _

theorem traceZeroSet_finite (X : ℝ) : (traceZeroSet X).Finite := by
  rw [traceZeroSet_eq]; exact ((pairs_finite X).subset fun _ h => h.1).image _

theorem splitSet_finite (X : ℝ) : (splitSet X).Finite := by
  rw [splitSet_eq]; exact ((pairs_finite X).subset fun _ h => h.1).image _

/-- `A₀(X) + #{split} = Σ_{1 ≤ N ≤ X} r(N)`. -/
theorem A₀_add_split (X : ℝ) :
    A₀ X + Nat.card (splitSet X) = ∑ N ∈ Finset.Icc 1 ⌊X⌋, r N := by
  have hc : Set.Finite {q | q ∈ pairs X ∧
      HasCyclicCubicGaloisGroup ((toCubic q).map (Int.castRingHom ℚ))} :=
    (pairs_finite X).subset fun _ h => h.1
  have hs : Set.Finite {q | q ∈ pairs X ∧ ((toCubic q).map (Int.castRingHom ℚ)).Splits} :=
    (pairs_finite X).subset fun _ h => h.1
  have hd : Disjoint {q | q ∈ pairs X ∧
      HasCyclicCubicGaloisGroup ((toCubic q).map (Int.castRingHom ℚ))}
      {q | q ∈ pairs X ∧ ((toCubic q).map (Int.castRingHom ℚ)).Splits} :=
    Set.disjoint_left.mpr fun q h h' => not_cyclic_and_splits _ h.2 h'.2
  have hu : {q | q ∈ pairs X ∧
      HasCyclicCubicGaloisGroup ((toCubic q).map (Int.castRingHom ℚ))} ∪
      {q | q ∈ pairs X ∧ ((toCubic q).map (Int.castRingHom ℚ)).Splits} = pairs X := by
    ext q
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases (isSquare_iff h.1).mp h.2.2 with hc | hs
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hs⟩
  rw [← ncard_pairs, A₀, Nat.card_coe_set_eq, Nat.card_coe_set_eq, traceZeroSet_eq, splitSet_eq,
    Set.ncard_image_of_injective _ toCubic_injective,
    Set.ncard_image_of_injective _ toCubic_injective, ← Set.ncard_union_eq hd hc hs, hu]

end Cubic.Counting.TraceZeroSplitting
