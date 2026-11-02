import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.Normal.Basic
import CubicTargets.BoxHeight.XiaoUpperBound
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Polynomials with roots in a fixed cyclic cubic field

Supporting step for the box-height lower bound. For a number field `K`, and `α ∈ 𝒪_K`,
`mulHeight₁ α = Π_φ max(|φ(α)|, 1)` over the complex embeddings `φ`, the Mahler measure of
`α` (the finite places contribute `1`). For a cyclic cubic `K` and `α ∉ ℤ`, the minimal
polynomial of `α` is `Π_φ (t - φ(α))`, a monic integral cubic with Galois group `C₃` whose
coefficients are at most `3 M(α)` in absolute value; at most three `α` share it. The rational
integers `m` have `M(m) = max(|m|, 1)³`.
-/

noncomputable section

namespace Cubic.BoxHeight.FieldPolynomials

open NumberField Polynomial

variable {K : Type*} [Field K] [NumberField K]

/-- The Mahler measure `Π_φ max(|φ(x)|, 1)`. -/
def mahler (x : K) : ℝ := ∏ φ : K →+* ℂ, max ‖φ x‖ 1

theorem prod_places_eq_prod_embeddings (g : InfinitePlace K → ℝ) :
    ∏ w : InfinitePlace K, g w ^ InfinitePlace.mult w = ∏ φ : K →+* ℂ, g (InfinitePlace.mk φ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => g (InfinitePlace.mk φ))]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]),
    Finset.prod_const, InfinitePlace.card_filter_mk_eq]

theorem mulHeight₁_eq_mahler (x : 𝓞 K) : Height.mulHeight₁ (x : K) = mahler (x : K) := by
  rw [NumberField.mulHeight₁_eq]
  have hfin : ∏ᶠ v : FinitePlace K, max (v (x : K)) 1 = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => max_eq_right ?_
    exact FinitePlace.norm_embedding_eq v (x : K) ▸ FinitePlace.norm_le_one v.maximalIdeal x
  rw [hfin, mul_one, prod_places_eq_prod_embeddings (fun w => max (w (x : K)) 1), mahler]
  rfl

/-! ### Cubic fields -/

variable (h3 : Module.finrank ℚ K = 3)
include h3

theorem natDegree_minpoly {x : K} (hx : x ∉ (algebraMap ℚ K).range) :
    (minpoly ℚ x).natDegree = 3 := by
  have hd := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  rw [h3] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd (minpoly.natDegree_eq_one_iff.mp h) hx
  · exact h

theorem card_gal_minpoly [Normal ℚ K] {x : K} (hx : x ∉ (algebraMap ℚ K).range) :
    Nat.card (minpoly ℚ x).Gal = 3 := by
  set f := minpoly ℚ x
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hirr : Irreducible f := minpoly.irreducible hint
  have hsep : f.Separable := hirr.separable
  rw [Polynomial.Gal.card_of_separable hsep]
  have hdeg := natDegree_minpoly h3 hx
  -- `[SF : ℚ] ≤ 3`: the splitting field embeds in `K`
  have hsplitK : (f.map (algebraMap ℚ K)).Splits := Normal.splits inferInstance x
  set lift := Polynomial.SplittingField.lift f hsplitK
  have hle : Module.finrank ℚ f.SplittingField ≤ 3 := by
    rw [← h3]
    exact LinearMap.finrank_le_finrank_of_injective (f := lift.toLinearMap) lift.injective
  -- `3 ∣ [SF : ℚ]`: the splitting field contains a root of `f`
  obtain ⟨y, hy⟩ := Polynomial.Splits.exists_eval_eq_zero
    (Polynomial.SplittingField.splits f) (by
      rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hirr.ne_zero, hdeg]; decide)
  have hmin : minpoly ℚ y = f := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (minpoly.monic hint)).symm
    rwa [Polynomial.eval_map_algebraMap] at hy
  have hdvd := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ) y)
  rw [hmin, hdeg] at hdvd
  have hpos : 0 < Module.finrank ℚ f.SplittingField := Module.finrank_pos
  obtain ⟨c, hc⟩ := hdvd
  rcases c with _ | _ | c <;> omega

theorem cyclic_minpoly [Normal ℚ K] {x : K} (hx : x ∉ (algebraMap ℚ K).range) :
    Cubic.QuadraticCorrespondence.CorrespondencePolynomials.HasCyclicCubicGaloisGroup
      (minpoly ℚ x) :=
  ⟨mulEquivOfPrimeCardEq (p := 3) (card_gal_minpoly h3 hx) (by simp [Nat.card_eq_fintype_card])⟩

theorem map_minpoly_eq_prod {x : K} (hx : x ∉ (algebraMap ℚ K).range) :
    (minpoly ℚ x).map (algebraMap ℚ ℂ) = ∏ φ : K →+* ℂ, (X - C (φ x)) := by
  classical
  set P := (minpoly ℚ x).map (algebraMap ℚ ℂ)
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hsep : (minpoly ℚ x).Separable := (minpoly.irreducible hint).separable
  have hmon : P.Monic := (minpoly.monic hint).map _
  have hspl : P.Splits := IsAlgClosed.splits P
  have hnd : P.roots.Nodup := Polynomial.nodup_roots (hsep.map)
  have hcard : P.roots.card = 3 := by
    rw [splits_iff_card_roots.mp hspl, natDegree_map, natDegree_minpoly h3 hx]
  set g : (K →+* ℂ) → ℂ := fun φ => φ x
  have hmem : ∀ a : ℂ, a ∈ P.roots ↔ a ∈ Finset.univ.image g := by
    intro a
    have h := congrArg (a ∈ ·) (NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ x)
    simp only [Set.mem_range, Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.aroots_def] at h
    simp only [Finset.mem_image, Finset.mem_univ, true_and, g]
    exact h.to_iff.symm
  have himg : (Finset.univ.image g).card = 3 := by
    rw [← hcard, ← Multiset.toFinset_card_of_nodup hnd]
    congr 1; ext a; rw [Multiset.mem_toFinset, hmem]
  have hinj : Function.Injective g := by
    have hc : (Finset.univ : Finset (K →+* ℂ)).card = 3 := by
      rw [Finset.card_univ, NumberField.Embeddings.card, h3]
    have := Finset.card_image_iff.mp (himg.trans hc.symm)
    exact fun a b hab => this (Finset.mem_coe.mpr (Finset.mem_univ a))
      (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  have hroots : P.roots = Multiset.map g Finset.univ.val := by
    refine (Multiset.Nodup.ext hnd (Multiset.Nodup.map hinj Finset.univ.nodup)).mpr fun a => ?_
    rw [hmem, Finset.mem_image]
    simp only [Multiset.mem_map, Finset.mem_val]
  rw [hspl.eq_prod_roots_of_monic hmon, hroots, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-! ### The integral minimal polynomial -/

omit h3 in
theorem minpoly_int_map (x : 𝓞 K) :
    (minpoly ℤ (x : K)).map (algebraMap ℤ ℚ) = minpoly ℚ (x : K) :=
  (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (x.2)).symm

theorem minpoly_int_eq_monicCubic {x : 𝓞 K} (hx : (x : K) ∉ (algebraMap ℚ K).range) :
    minpoly ℤ (x : K) = Cubic.Counting.GeneralMonicData.monicCubic
      ((minpoly ℤ (x : K)).coeff 2) ((minpoly ℤ (x : K)).coeff 1) ((minpoly ℤ (x : K)).coeff 0) := by
  set f := minpoly ℤ (x : K)
  have hmon : f.Monic := minpoly.monic x.2
  have hdeg : f.natDegree = 3 := by
    rw [← hmon.natDegree_map (algebraMap ℤ ℚ), minpoly_int_map]
    exact natDegree_minpoly h3 hx
  conv_lhs => rw [hmon.as_sum, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Cubic.Counting.GeneralMonicData.monicCubic,
    pow_zero, pow_one, mul_one, zero_add]
  ring

/-- The coefficients of the minimal polynomial are at most `3 M(α)`. -/
theorem coeff_bounds {x : 𝓞 K} (hx : (x : K) ∉ (algebraMap ℚ K).range) (i : ℕ) (hi : i ≤ 2) :
    |((minpoly ℤ (x : K)).coeff i : ℝ)| ≤ 3 * mahler (x : K) := by
  set f := minpoly ℤ (x : K)
  have hcard : Fintype.card (K →+* ℂ) = 3 := by rw [NumberField.Embeddings.card, h3]
  set e : Fin 3 ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq hcard).symm
  set r : Fin 3 → ℂ := fun i => e i (x : K)
  have hM : mahler (x : K) = max ‖r 0‖ 1 * max ‖r 1‖ 1 * max ‖r 2‖ 1 := by
    rw [mahler, ← Fintype.prod_equiv e (fun i => max ‖r i‖ 1) _ (fun _ => rfl), Fin.prod_univ_three]
  have hprod : ∏ φ : K →+* ℂ, (X - C (φ (x : K))) = (X - C (r 0)) * (X - C (r 1)) * (X - C (r 2)) := by
    rw [← Fintype.prod_equiv e (fun i => X - C (r i)) _ (fun _ => rfl), Fin.prod_univ_three]
  have hmap : f.map (Int.castRingHom ℂ) = (minpoly ℚ (x : K)).map (algebraMap ℚ ℂ) := by
    rw [← minpoly_int_map, Polynomial.map_map]
    congr 1
  rw [map_minpoly_eq_prod h3 hx, hprod] at hmap
  have hfm : f = Cubic.Counting.GeneralMonicData.monicCubic (f.coeff 2) (f.coeff 1) (f.coeff 0) :=
    minpoly_int_eq_monicCubic h3 hx
  rw [hfm] at hmap
  set c2 := f.coeff 2
  set c1 := f.coeff 1
  set c0 := f.coeff 0
  have hexp : (X - C (r 0)) * (X - C (r 1)) * (X - C (r 2)) =
      X ^ 3 + C (-(r 0 + r 1 + r 2)) * X ^ 2 + C (r 0 * r 1 + r 0 * r 2 + r 1 * r 2) * X +
        C (-(r 0 * r 1 * r 2)) := by
    simp only [map_neg, map_add, map_mul]; ring
  rw [hexp] at hmap
  simp only [Cubic.Counting.GeneralMonicData.monicCubic, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, eq_intCast] at hmap
  have hco : ∀ n, ((X ^ 3 + C (c2 : ℂ) * X ^ 2 + C (c1 : ℂ) * X + C (c0 : ℂ)) : ℂ[X]).coeff n =
      ((X ^ 3 + C (-(r 0 + r 1 + r 2)) * X ^ 2 + C (r 0 * r 1 + r 0 * r 2 + r 1 * r 2) * X +
        C (-(r 0 * r 1 * r 2))) : ℂ[X]).coeff n := fun n => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) hmap
    simpa using this
  have e2 := hco 2
  have e1 := hco 1
  have e0 := hco 0
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e2 e1 e0
  norm_num at e2 e1 e0
  -- the bounds
  have m0 := le_max_left ‖r 0‖ 1
  have m1 := le_max_left ‖r 1‖ 1
  have m2 := le_max_left ‖r 2‖ 1
  have o0 := le_max_right ‖r 0‖ 1
  have o1 := le_max_right ‖r 1‖ 1
  have o2 := le_max_right ‖r 2‖ 1
  set a := max ‖r 0‖ 1
  set b := max ‖r 1‖ 1
  set c := max ‖r 2‖ 1
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le o0 o1
  have ha_le : a ≤ a * b * c := by nlinarith
  have hb_le : b ≤ a * b * c := by nlinarith
  have hc_le : c ≤ a * b * c := by nlinarith
  have hab_le : a * b ≤ a * b * c := by nlinarith
  have hac_le : a * c ≤ a * b * c := by nlinarith
  have hbc_le : b * c ≤ a * b * c := by nlinarith
  rw [hM]
  have n0 := norm_nonneg (r 0)
  have n1 := norm_nonneg (r 1)
  have n2 := norm_nonneg (r 2)
  interval_cases i
  · have : |(c0 : ℝ)| = ‖r 0 * r 1 * r 2‖ := by
      rw [← Complex.norm_intCast, e0, norm_neg]
    rw [this, norm_mul, norm_mul]
    have : ‖r 0‖ * ‖r 1‖ * ‖r 2‖ ≤ a * b * c :=
      mul_le_mul (mul_le_mul m0 m1 n1 (by linarith)) m2 n2 (by nlinarith)
    nlinarith
  · have : |(c1 : ℝ)| = ‖r 0 * r 1 + r 0 * r 2 + r 1 * r 2‖ := by
      rw [← Complex.norm_intCast, e1]
    rw [this]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h01 : ‖r 0‖ * ‖r 1‖ ≤ a * b := mul_le_mul m0 m1 n1 (by linarith)
    have h02 : ‖r 0‖ * ‖r 2‖ ≤ a * c := mul_le_mul m0 m2 n2 (by linarith)
    have h12 : ‖r 1‖ * ‖r 2‖ ≤ b * c := mul_le_mul m1 m2 n2 (by linarith)
    linarith
  · have : |(c2 : ℝ)| = ‖r 0 + r 1 + r 2‖ := by
      rw [← Complex.norm_intCast, e2, show -r 2 + (-r 1 + -r 0) = -(r 0 + r 1 + r 2) by ring,
        norm_neg]
    rw [this]
    refine (norm_add₃_le).trans ?_
    linarith

end Cubic.BoxHeight.FieldPolynomials
