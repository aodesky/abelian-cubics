import Cubic.BoxAsymptotic.Parametrization
import Cubic.Counting.CyclicCubicField
import Cubic.Counting.CubicDiscriminantSquare
import Cubic.Counting.TraceZeroSplitting
import Cubic.BoxHeight.XiaoCounterexample

/-!
# Separable cubics with square discriminant

A monic integral cubic with nonzero square discriminant is either cyclic or split over `ℚ`,
and not both; conversely a cyclic cubic has nonzero square discriminant. So the coefficient
triples in the box with nonzero square discriminant are the cyclic ones (`boxSet H`) and
the separable split ones.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.SquareDiscriminant

open Polynomial Cubic.Counting.GeneralMonicData Cubic.BoxAsymptotic.Parametrization
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- `t³ + a₂t² + a₁t + a₀` as a rational `Cubic`. -/
def cubicQ (a₂ a₁ a₀ : ℤ) : _root_.Cubic ℚ := ⟨1, a₂, a₁, a₀⟩

theorem toPoly_cubicQ (a₂ a₁ a₀ : ℤ) :
    (cubicQ a₂ a₁ a₀).toPoly = (monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ) := by
  simp [cubicQ, _root_.Cubic.toPoly, monicCubic]

theorem discr_cubicQ (a₂ a₁ a₀ : ℤ) : (cubicQ a₂ a₁ a₀).discr = (Parametrization.disc a₂ a₁ a₀ : ℚ) := by
  simp [cubicQ, _root_.Cubic.discr, Parametrization.disc]

theorem natDegree_map (a₂ a₁ a₀ : ℤ) :
    ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ)).natDegree = 3 := by
  rw [← toPoly_cubicQ]
  exact _root_.Cubic.natDegree_of_a_ne_zero (by simp [cubicQ])

/-- A cubic with Galois group `C₃` has no rational root. -/
theorem not_isRoot_of_cyclic {f : ℚ[X]} (hdeg : f.natDegree = 3)
    (hc : HasCyclicCubicGaloisGroup f) (r : ℚ) : ¬ f.IsRoot r := by
  classical
  intro hr
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    rw [hq, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hqdeg : q.natDegree ≤ 2 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero r) hq0, natDegree_X_sub_C] at hdeg
    omega
  rw [hq] at hc
  obtain ⟨e⟩ := hc
  have h3 : Fintype.card ((X - C r) * q).Gal = 3 := by
    rw [Fintype.card_congr e.toEquiv]; rfl
  haveI : Unique (X - C r).Gal := Polynomial.Gal.uniqueGalOfSplits _ (Splits.X_sub_C r)
  have hle := Fintype.card_le_of_injective _ (Polynomial.Gal.restrictProd_injective (X - C r) q)
  have h1 : Fintype.card (X - C r).Gal = 1 := Fintype.card_unique
  rw [Fintype.card_prod, h1, one_mul, h3] at hle
  have := Cubic.Counting.CyclicCubicField.card_gal_le_two q hqdeg
  omega

theorem irreducible_of_cyclic {f : ℚ[X]} (hdeg : f.natDegree = 3)
    (hc : HasCyclicCubicGaloisGroup f) : Irreducible f :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide) (not_isRoot_of_cyclic hdeg hc)

/-- A cyclic cubic has nonzero discriminant. -/
theorem disc_ne_zero_of_cyclic {a₂ a₁ a₀ : ℤ}
    (hc : HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ))) :
    Parametrization.disc a₂ a₁ a₀ ≠ 0 := by
  intro h0
  set P := cubicQ a₂ a₁ a₀
  have hirr := irreducible_of_cyclic (natDegree_map a₂ a₁ a₀) hc
  rw [← toPoly_cubicQ] at hirr
  have hsep : P.toPoly.Separable := hirr.separable
  let L := P.toPoly.SplittingField
  have hsL : (P.toPoly.map (algebraMap ℚ L)).Splits := SplittingField.splits P.toPoly
  have ha : P.a ≠ 0 := by simp [P, cubicQ]
  have hnd : (_root_.Cubic.map (algebraMap ℚ L) P).roots.Nodup := by
    rw [_root_.Cubic.roots, _root_.Cubic.map_toPoly]
    exact nodup_roots hsep.map
  have := (_root_.Cubic.discr_ne_zero_iff_roots_nodup ha hsL).mpr hnd
  rw [discr_cubicQ, h0] at this
  exact this (by simp)

/-- Coefficient triples in the box with nonzero square discriminant. -/
def sqSet (H : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {t | (|t.1| : ℝ) ≤ H ∧ (|t.2.1| : ℝ) ≤ H ∧ (|t.2.2| : ℝ) ≤ H ∧
    Parametrization.disc t.1 t.2.1 t.2.2 ≠ 0 ∧ IsSquare (Parametrization.disc t.1 t.2.1 t.2.2)}

/-- Separable split monic cubics in the box. -/
def splitSet (H : ℝ) : Set ℤ[X] :=
  {f | ∃ a₂ a₁ a₀ : ℤ, f = monicCubic a₂ a₁ a₀ ∧ (|a₂| : ℝ) ≤ H ∧ (|a₁| : ℝ) ≤ H ∧
    (|a₀| : ℝ) ≤ H ∧ Parametrization.disc a₂ a₁ a₀ ≠ 0 ∧
    (f.map (Int.castRingHom ℚ)).Splits}

theorem isSquare_of_cyclic {a₂ a₁ a₀ : ℤ}
    (hc : HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ))) :
    IsSquare (Parametrization.disc a₂ a₁ a₀) := by
  rw [← toPoly_cubicQ] at hc
  obtain ⟨q, hq⟩ := Cubic.Counting.CubicDiscriminantSquare.discr_square_of_cyclic (by simp [cubicQ]) hc
  rw [discr_cubicQ] at hq
  exact Rat.isSquare_intCast_iff.mp ⟨q, by rw [hq]; ring⟩

theorem isSquare_of_splits {a₂ a₁ a₀ : ℤ}
    (hs : ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ)).Splits) :
    IsSquare (Parametrization.disc a₂ a₁ a₀) := by
  rw [← toPoly_cubicQ] at hs
  obtain ⟨q, hq⟩ := Cubic.Counting.CubicDiscriminantSquare.discr_square_of_splits (by simp [cubicQ]) hs
  rw [discr_cubicQ] at hq
  exact Rat.isSquare_intCast_iff.mp ⟨q, by rw [hq]; ring⟩

theorem cyclic_or_splits {a₂ a₁ a₀ : ℤ} (h0 : Parametrization.disc a₂ a₁ a₀ ≠ 0)
    (hsq : IsSquare (Parametrization.disc a₂ a₁ a₀)) :
    HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ)) ∨
      ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ)).Splits := by
  obtain ⟨d, hd⟩ := hsq
  rw [← toPoly_cubicQ]
  refine Cubic.Counting.CubicDiscriminantSquare.cyclic_or_splits_of_discr (by simp [cubicQ]) (d := d) ?_ ?_
  · rw [discr_cubicQ, hd]; push_cast; ring
  · rintro h; apply h0; rw [hd]; simp [show d = 0 by exact_mod_cast h]

theorem monicCubic_injective {a₂ a₁ a₀ b₂ b₁ b₀ : ℤ}
    (h : monicCubic a₂ a₁ a₀ = monicCubic b₂ b₁ b₀) : a₂ = b₂ ∧ a₁ = b₁ ∧ a₀ = b₀ := by
  have h2 := congrArg (fun f => f.coeff 2) h
  have h1 := congrArg (fun f => f.coeff 1) h
  have h0 := congrArg (fun f => f.coeff 0) h
  simp only [Cubic.Counting.GeneralHeightReduction.monicCubic_coeff_two, Cubic.Counting.GeneralHeightReduction.monicCubic_coeff_one,
    Cubic.Counting.GeneralHeightReduction.monicCubic_coeff_zero] at h2 h1 h0
  exact ⟨h2, h1, h0⟩

theorem sqSet_finite (H : ℝ) : (sqSet H).Finite := by
  set B := ⌊H⌋
  refine ((Set.finite_Icc (-B) B).prod ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B))).subset ?_
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, -⟩
  have key : ∀ x : ℤ, (|x| : ℝ) ≤ H → x ∈ Set.Icc (-B) B := fun x hx => by
    rw [abs_le] at hx
    constructor
    · have : -x ≤ B := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr hx.2
  exact ⟨key a ha, key b hb, key c hc⟩

/-- The triple `(a₂, a₁, a₀)` of `(a₂, a₁, a₀, d)`. -/
def proj (y : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (y.1, y.2.1, y.2.2.1)

/-- `#boxSq = 2 #sqSet`: each triple has the two square roots `±d`. -/
theorem card_boxSq (H : ℝ) : Nat.card (boxSq H) = 2 * Nat.card (sqSet H) := by
  set P := {y | y ∈ boxSq H ∧ 0 < y.2.2.2}
  set N := {y | y ∈ boxSq H ∧ y.2.2.2 < 0}
  have hP : Set.BijOn proj P (sqSet H) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b, c, d⟩ ⟨⟨ha, hb, hc, hd0, hd⟩, -⟩
      dsimp only at hd
      exact ⟨ha, hb, hc, by dsimp only [proj]; rw [hd]; positivity,
        ⟨d, by dsimp only [proj]; rw [hd]; ring⟩⟩
    · rintro ⟨a, b, c, d⟩ ⟨⟨-, -, -, -, hd⟩, hdp⟩ ⟨a', b', c', d'⟩ ⟨⟨-, -, -, -, hd'⟩, hdp'⟩ he
      simp only [proj, Prod.mk.injEq] at he hd hd' hdp hdp'
      obtain ⟨rfl, rfl, rfl⟩ := he
      have : d ^ 2 = d' ^ 2 := by rw [← hd, ← hd']
      have := (sq_eq_sq₀ hdp.le hdp'.le).mp this
      rw [this]
    · rintro ⟨a, b, c⟩ ⟨ha, hb, hc, h0, r, hr⟩
      refine ⟨(a, b, c, |r|), ⟨⟨ha, hb, hc, ?_, ?_⟩, ?_⟩, rfl⟩
      · rw [abs_ne_zero]; rintro rfl; simp at hr; exact h0 hr
      · simp only; rw [sq_abs, hr]; ring
      · simp only; rw [abs_pos]; rintro rfl; simp at hr; exact h0 hr
  set flip : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ := fun y => (y.1, y.2.1, y.2.2.1, -y.2.2.2)
  have hN : Set.BijOn flip N P := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b, c, d⟩ ⟨⟨ha, hb, hc, hd0, hd⟩, hdn⟩
      exact ⟨⟨ha, hb, hc, neg_ne_zero.mpr hd0, by simp only at hd ⊢; rw [hd]; ring⟩,
        by simp only at hdn ⊢; linarith⟩
    · intro y _ z _ h
      simp only [flip, Prod.mk.injEq, neg_inj] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))
    · rintro ⟨a, b, c, d⟩ ⟨⟨ha, hb, hc, hd0, hd⟩, hdp⟩
      refine ⟨(a, b, c, -d), ⟨⟨ha, hb, hc, neg_ne_zero.mpr hd0, ?_⟩, ?_⟩, ?_⟩
      · simp only at hd ⊢; rw [hd]; ring
      · simp only at hdp ⊢; linarith
      · simp [flip]
  have hPf : P.Finite := Set.Finite.of_finite_image (hP.image_eq ▸ sqSet_finite H) hP.injOn
  have hNf : N.Finite := Set.Finite.of_finite_image (hN.image_eq ▸ hPf) hN.injOn
  have hunion : boxSq H = P ∪ N := by
    ext y
    constructor
    · intro hy
      rcases lt_or_gt_of_ne hy.2.2.2.1 with h | h
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint P N := Set.disjoint_left.mpr fun y hp hn => by
    have := hp.2; have := hn.2; linarith
  rw [Nat.card_coe_set_eq, hunion, Set.ncard_union_eq hdisj hPf hNf, Nat.card_coe_set_eq,
    ← Set.InjOn.ncard_image hN.injOn, hN.image_eq, ← Set.InjOn.ncard_image hP.injOn,
    hP.image_eq]
  ring

/-- The monic cubic with a coefficient triple. -/
def mc (t : ℤ × ℤ × ℤ) : ℤ[X] := monicCubic t.1 t.2.1 t.2.2

theorem mc_injective : Function.Injective mc := fun t u h => by
  obtain ⟨h2, h1, h0⟩ := monicCubic_injective h
  exact Prod.ext h2 (Prod.ext h1 h0)

/-- `#sqSet = N_□(H) + #(split)`. -/
theorem card_sqSet (H : ℝ) :
    Nat.card (sqSet H) = CubicTargets.BoxHeight.boxCount H + Nat.card (splitSet H) := by
  set Cy := {t | t ∈ sqSet H ∧ HasCyclicCubicGaloisGroup ((mc t).map (Int.castRingHom ℚ))}
  set Sp := {t | t ∈ sqSet H ∧ ((mc t).map (Int.castRingHom ℚ)).Splits}
  have hCy : Set.BijOn mc Cy (CubicTargets.BoxHeight.boxSet H) := by
    refine ⟨?_, mc_injective.injOn, ?_⟩
    · rintro ⟨a, b, c⟩ ⟨⟨ha, hb, hc, -⟩, hcy⟩
      exact ⟨⟨a, b, c, rfl, ha, hb, hc⟩, hcy⟩
    · rintro f ⟨⟨a, b, c, rfl, ha, hb, hc⟩, hcy⟩
      exact ⟨(a, b, c), ⟨⟨ha, hb, hc, disc_ne_zero_of_cyclic hcy, isSquare_of_cyclic hcy⟩, hcy⟩, rfl⟩
  have hSp : Set.BijOn mc Sp (splitSet H) := by
    refine ⟨?_, mc_injective.injOn, ?_⟩
    · rintro ⟨a, b, c⟩ ⟨⟨ha, hb, hc, h0, -⟩, hs⟩
      exact ⟨a, b, c, rfl, ha, hb, hc, h0, hs⟩
    · rintro f ⟨a, b, c, rfl, ha, hb, hc, h0, hs⟩
      exact ⟨(a, b, c), ⟨⟨ha, hb, hc, h0, isSquare_of_splits hs⟩, hs⟩, rfl⟩
  have hunion : sqSet H = Cy ∪ Sp := by
    ext t
    constructor
    · intro ht
      rcases cyclic_or_splits ht.2.2.2.1 ht.2.2.2.2 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint Cy Sp := Set.disjoint_left.mpr fun t hc hs =>
    Cubic.Counting.TraceZeroSplitting.not_cyclic_and_splits _ hc.2 hs.2
  have hfin := sqSet_finite H
  rw [Nat.card_coe_set_eq, hunion, Set.ncard_union_eq hdisj (hfin.subset fun _ h => h.1)
    (hfin.subset fun _ h => h.1), ← Set.InjOn.ncard_image hCy.injOn, hCy.image_eq,
    ← Set.InjOn.ncard_image hSp.injOn, hSp.image_eq, CubicTargets.BoxHeight.boxCount,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq]

/-- The exact parametrization: `#{admissible (s, β), B ≠ 0, in the box} = 2 (N_□(H) + #split)`. -/
theorem card_pairs_eq (H : ℝ) :
    Nat.card (Parametrization.pairs H) =
      2 * (CubicTargets.BoxHeight.boxCount H + Nat.card (splitSet H)) := by
  rw [Parametrization.card_pairs, card_boxSq, card_sqSet]

end Cubic.BoxAsymptotic.SquareDiscriminant
