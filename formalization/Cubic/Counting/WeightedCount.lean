import Cubic.Counting.SplitCount
import Cubic.Counting.CyclicFibre
import Cubic.ToricHeights.CanonicalHeight
import Cubic.QuadraticCorrespondence.QuotientCubicClassification
import Cubic.Counting.EllipseLatticeCount
import CubicTargets.Counting.WeightedPolynomialCount
import Cubic.PoissonSummation.HeightCountingSeries
import Cubic.PoissonSummation.IntegralPointComparison

/-!
# `eqn:weightedPolynomialCount`

The exact count assigns two points to each cyclic cubic and one cyclic-shift
orbit to each integral split triple. Normality follows from the general
`lemma:normalityCriterion`: an integral trace-one characteristic polynomial
has `1 - 3a ≠ 0`. `exact_count` records this finite counting identity.
The exact-label theorem then inserts the proved ellipse lattice estimate and
sets `H = √X`, giving the current asymptotic with error `O(√X)`.
-/

noncomputable section

namespace Cubic.Counting.WeightedCount

open Polynomial Cubic.OrbitParametrization Cubic.OrbitParametrization.C3Algebra
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.Counting.SplitPoints Cubic.Counting.SplitCount
open CubicTargets.Counting.EllipseLatticeCount

abbrev Pts := quotientFixedRing →ₐ[ℚ] ℚ

/-- The height index `H(P)² = 1-3a`. -/
def hindex (P : Pts) : ℝ := 1 - 3 * (P linearCoefficient : ℝ)

/-- Integral points of height at most `H`. -/
def IP (H : ℝ) : Set Pts :=
  {P | Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P ∧ hindex P ≤ H ^ 2}

/-- Those with rationally split characteristic polynomial. -/
def IPs (H : ℝ) : Set Pts := {P | P ∈ IP H ∧ (characteristicPolynomial P).Splits}

/-- Those with cyclic characteristic polynomial. -/
def IPc (H : ℝ) : Set Pts :=
  {P | P ∈ IP H ∧ HasCyclicCubicGaloisGroup (characteristicPolynomial P)}

theorem triple_charPoly (v : Triple) :
    characteristicPolynomial (triplePoint v) =
      (X - C (v.val 0 : ℚ)) * (X - C (v.val 1 : ℚ)) * (X - C (v.val 2 : ℚ)) := by
  have hsum : (v.val 0 : ℚ) + v.val 1 + v.val 2 = 1 := by exact_mod_cast v.property
  rw [characteristicPolynomial, cubic, triplePoint_linear, triplePoint_constant]
  simp only [OrbitParametrization.secondCoeff, OrbitParametrization.constantCoeff]
  push_cast
  have h1 : (X : ℚ[X]) ^ 2 = C ((v.val 0 : ℚ) + v.val 1 + v.val 2) * X ^ 2 := by
    rw [hsum, map_one, one_mul]
  rw [h1]
  simp only [map_add, map_mul, map_neg]
  ring

theorem triplePoint_mem (H : ℝ) (v : Triple) (hv : v ∈ boundedTriples H) :
    triplePoint v ∈ IPs H := by
  refine ⟨⟨triplePoint_integral v, ?_⟩, ?_⟩
  · change 1 - 3 * ((triplePoint v linearCoefficient : ℚ) : ℝ) ≤ H ^ 2
    rw [triplePoint_linear]
    have hv' : 1 - 3 * ((secondCoeff (v.val 0) (v.val 1) (v.val 2) : ℤ) : ℝ) ≤ H ^ 2 := hv
    exact_mod_cast hv'
  · rw [triple_charPoly]
    exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

theorem image_triples (H : ℝ) : triplePoint '' boundedTriples H = IPs H := by
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact triplePoint_mem H v hv
  · rintro ⟨⟨hint, hle⟩, hs⟩
    obtain ⟨v, rfl⟩ := exists_triple P hint hs
    refine ⟨v, ?_, rfl⟩
    change 1 - 3 * ((secondCoeff (v.val 0) (v.val 1) (v.val 2) : ℤ) : ℝ) ≤ H ^ 2
    have := hle
    change 1 - 3 * ((triplePoint v linearCoefficient : ℚ) : ℝ) ≤ H ^ 2 at this
    rw [triplePoint_linear] at this
    exact_mod_cast this

/-- A map whose fibres all have `k` elements. -/
theorem card_eq_mul_of_fibres {α β : Type*} [Finite β] (f : α → β) (k : ℕ) (hk : k ≠ 0)
    (hf : ∀ b, Nat.card {a // f a = b} = k) : Nat.card α = Nat.card β * k := by
  haveI := Fintype.ofFinite β
  haveI : ∀ b, Finite {a // f a = b} := fun b =>
    Nat.finite_of_card_ne_zero (by rw [hf b]; exact hk)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp [hf, Nat.card_eq_fintype_card]

theorem boundedTriples_finite (H : ℝ) (hH : 1 ≤ H) : (boundedTriples H).Finite := by
  have hfin := (Cubic.Counting.EllipseLatticeCount.«eqn:ellipseLatticeCount»).1 H hH
  haveI := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (triplesEquiv H))

theorem IPs_finite (H : ℝ) (hH : 1 ≤ H) : (IPs H).Finite := by
  rw [← image_triples]
  exact (boundedTriples_finite H hH).image _

/-- Split side: `#(E_H° ∩ ℤ²) = 3 · #(split points of height ≤ H)`. -/
theorem card_split (H : ℝ) (hH : 1 ≤ H) :
    Nat.card (latticePoints H) = Nat.card (IPs H) * 3 := by
  rw [← boundedTriples_card]
  haveI := (IPs_finite H hH).to_subtype
  let f : boundedTriples H → IPs H := fun w => ⟨triplePoint w.val, triplePoint_mem H w.val w.property⟩
  apply card_eq_mul_of_fibres f 3 (by norm_num)
  intro b
  have hb : b.val ∈ triplePoint '' boundedTriples H := by rw [image_triples]; exact b.property
  obtain ⟨v, hv, hvb⟩ := hb
  rw [← SplitCount.fibre_card H ⟨v, hv⟩]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro w
  simp only [f, Subtype.ext_iff, hvb]

/-! ### The coefficient sum `Σ_{n ≤ H²} d_n` counts all integral points of height `≤ H` -/

section Coefficients

open Cubic.PoissonSummation Cubic.PoissonSummation.AdelicHeightZetaData
open Cubic.PoissonSummation.IntegralHeightIndex Cubic.PoissonSummation.HeightCountingSeries

theorem index_real (Q : IntegralRationalPoints) : ((index Q : ℕ) : ℝ) = hindex Q.val := by
  have h := congrArg (Int.cast : ℤ → ℝ) (index_cast Q)
  have hq : (Q.val linearCoefficient : ℚ) = ((Q.val linearCoefficient).num : ℚ) :=
    Rat.eq_num_of_isInt (linear_isInt Q)
  push_cast at h
  unfold hindex
  rw [hq]
  push_cast
  linarith

/-- `prop:canonicalHeight`: an integral point has toric height `√n` iff `1-3a = n`. -/
theorem height_eq_sqrt_iff (Q : IntegralRationalPoints) (n : ℕ) :
    HeightCountingData.pointHeight Q = (Real.sqrt n : ℂ) ↔ index Q = n := by
  have hint := (IntegralPointComparison.integralPoint_iff Q.val).mpr Q.property
  change AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal Q.val) = _ ↔ _
  rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 Q.val hint,
    Complex.ofReal_inj]
  change Real.sqrt (hindex Q.val) = _ ↔ _
  rw [← index_real, Real.sqrt_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _), Nat.cast_inj]

/-- The height fibre `d_n` is the fibre of `1-3a` over `n`. -/
def heightFibreEquiv (n : ℕ) : HeightCountingData.Fiber n ≃ IndexFiber n :=
  Equiv.subtypeEquivRight (fun Q => height_eq_sqrt_iff Q n)

/-- The fibre of the index map inside the points with index in `S` is an index fibre. -/
def fibreEquiv (S : Finset ℕ) (n : S) :
    {Q : {Q : IntegralRationalPoints // index Q ∈ S} // (⟨index Q.val, Q.property⟩ : S) = n} ≃
      IndexFiber n.val where
  toFun Q := ⟨Q.val.val, congrArg Subtype.val Q.property⟩
  invFun P := ⟨⟨P.val, by rw [P.property]; exact n.property⟩, Subtype.ext P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_count (S : Finset ℕ) :
    ∑ n ∈ S, HeightCountingData.count n =
      Nat.card {Q : IntegralRationalPoints // index Q ∈ S} := by
  let f : {Q : IntegralRationalPoints // index Q ∈ S} → S := fun Q => ⟨index Q.val, Q.property⟩
  haveI : ∀ n : S, Finite {Q // f Q = n} := fun n => by
    haveI := index_fiber_finite n.val
    exact Finite.of_equiv _ (fibreEquiv S n).symm
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [HeightCountingData.count, Nat.card_congr (heightFibreEquiv n)]
  exact (Nat.card_congr (fibreEquiv S n)).symm

theorem index_mem_iff (H : ℝ) (Q : IntegralRationalPoints) :
    index Q ∈ Finset.Icc 1 ⌊H ^ 2⌋₊ ↔ hindex Q.val ≤ H ^ 2 := by
  rw [Finset.mem_Icc, ← index_real, ← Nat.le_floor_iff (sq_nonneg H)]
  have := index_pos Q
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨this, h⟩

/-- `IP H` is the set of `D₀`-integral points of height at most `H` in the adelic sense. -/
def IPEquiv (H : ℝ) :
    IP H ≃ {Q : IntegralRationalPoints // index Q ∈ Finset.Icc 1 ⌊H ^ 2⌋₊} where
  toFun P := ⟨⟨P.val, (IntegralPointComparison.integralPoint_iff _).mp P.property.1⟩,
    (index_mem_iff H _).mpr P.property.2⟩
  invFun Q := ⟨Q.val.val, (IntegralPointComparison.integralPoint_iff _).mpr Q.val.property,
    (index_mem_iff H _).mp Q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_count_eq (H : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊H ^ 2⌋₊, HeightCountingData.count n = Nat.card (IP H) := by
  rw [sum_count, Nat.card_congr (IPEquiv H)]

theorem IP_finite (H : ℝ) : (IP H).Finite := by
  let S := Finset.Icc 1 ⌊H ^ 2⌋₊
  let f : {Q : IntegralRationalPoints // index Q ∈ S} → S := fun Q => ⟨index Q.val, Q.property⟩
  haveI : ∀ n : S, Finite {Q // f Q = n} := fun n => by
    haveI := index_fiber_finite n.val
    exact Finite.of_equiv _ (fibreEquiv S n).symm
  haveI : Finite {Q : IntegralRationalPoints // index Q ∈ S} :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv f)
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (IPEquiv H).symm)

end Coefficients

/-! ### Each cyclic polynomial has exactly two points -/

section Cyclic

open Cubic.Counting.PolynomialCountData CubicTargets.Counting.WeightedPolynomialCount

theorem traceOneCubic_coeff_one (a b : ℤ) : (PolynomialCountData.traceOneCubic a b).coeff 1 = a := by
  simp only [PolynomialCountData.traceOneCubic, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul,
    coeff_X_one, coeff_C]
  norm_num

theorem traceOneCubic_map (a b : ℤ) :
    (PolynomialCountData.traceOneCubic a b).map (Int.castRingHom ℚ) = cubic a b := by
  simp [PolynomialCountData.traceOneCubic, cubic]

/-- The integer cubic of an integral point. -/
def toPoly (P : Pts) : ℤ[X] :=
  PolynomialCountData.traceOneCubic (P linearCoefficient).num (P constantCoefficient).num

theorem toPoly_map (P : Pts) (hP : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P) :
    (toPoly P).map (Int.castRingHom ℚ) = characteristicPolynomial P := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P).mp hP
  rw [toPoly, traceOneCubic_map, characteristicPolynomial, ha, hb, Rat.num_intCast,
    Rat.num_intCast]

theorem height_le_iff (a : ℚ) (H : ℝ) (hH : 1 ≤ H) :
    Real.sqrt (1 - 3 * (a : ℝ)) ≤ H ↔ 1 - 3 * (a : ℝ) ≤ H ^ 2 :=
  Real.sqrt_le_left (by linarith)

theorem toPoly_mem (H : ℝ) (hH : 1 ≤ H) (P : Pts) (hP : P ∈ IPc H) : toPoly P ∈ countSet H := by
  have hmap := toPoly_map P hP.1.1
  refine ⟨⟨⟨_, _, rfl⟩, by rw [hmap]; exact hP.2⟩, ?_⟩
  have h1 : ((toPoly P).coeff 1 : ℝ) = ((P linearCoefficient : ℚ) : ℝ) := by
    have := congrArg (fun f : ℚ[X] => f.coeff 1) hmap
    simp only [coeff_map, characteristicPolynomial, cubic_coeff_one, eq_intCast] at this
    rw [← this]; push_cast; rfl
  rw [toricHeight, h1, height_le_iff _ H hH]
  exact hP.1.2

/-- The fibre of `toPoly` over `f = t³-t²+at+b` in `IPc H` is the set of all rational
points with characteristic polynomial `f`. -/
def cyclicFibreEquiv (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (hf : PolynomialCountData.traceOneCubic a b ∈ countSet H) :
    {P : IPc H // toPoly P.val = PolynomialCountData.traceOneCubic a b} ≃
      {P : Pts // characteristicPolynomial P = cubic a b} where
  toFun P := ⟨P.val.val, by
    rw [← toPoly_map _ P.val.property.1.1, P.property, traceOneCubic_map]⟩
  invFun P := by
    have ha : P.val linearCoefficient = a := by
      have := congrArg (fun f : ℚ[X] => f.coeff 1) P.property
      simpa only [characteristicPolynomial, cubic_coeff_one] using this
    have hb : P.val constantCoefficient = b := by
      have := congrArg (fun f : ℚ[X] => f.coeff 0) P.property
      simpa only [characteristicPolynomial, cubic_coeff_zero] using this
    have hint : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P.val :=
      (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P.val).mpr ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨P.val, ⟨hint, ?_⟩, ?_⟩, ?_⟩
    · have h2 := hf.2
      rw [toricHeight, traceOneCubic_coeff_one,
        show ((a : ℤ) : ℝ) = (((a : ℚ)) : ℝ) by push_cast; rfl, height_le_iff _ H hH] at h2
      change 1 - 3 * ((P.val linearCoefficient : ℚ) : ℝ) ≤ H ^ 2
      rw [ha]; exact h2
    · rw [P.property, ← traceOneCubic_map]; exact hf.1.2
    · change PolynomialCountData.traceOneCubic (P.val linearCoefficient).num
        (P.val constantCoefficient).num = _
      rw [ha, hb, Rat.num_intCast, Rat.num_intCast]
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cyclic side: `#{P ∈ IPc H} = 2 · #{f ∈ F : H(f) ≤ H}`. -/
theorem card_cyclic (H : ℝ) (hH : 1 ≤ H) :
    (countSet H).Finite ∧ Nat.card (IPc H) = Nat.card (countSet H) * 2 := by
  have hIPc : (IPc H).Finite := (IP_finite H).subset fun P hP => hP.1
  haveI := hIPc.to_subtype
  let g : IPc H → countSet H := fun P => ⟨toPoly P.val, toPoly_mem H hH P.val P.property⟩
  have hfib : ∀ f : countSet H, Nat.card {P // g P = f} = 2 := by
    rintro ⟨f, hf⟩
    obtain ⟨⟨a, b, rfl⟩, hc⟩ := hf.1
    rw [traceOneCubic_map] at hc
    rw [← CyclicFibre.fibre_card _ _ hc, ← Nat.card_congr (cyclicFibreEquiv H hH a b hf)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro P
    simp only [g, Subtype.ext_iff]
  have hsurj : Function.Surjective g := fun f => by
    have : 0 < Nat.card {P // g P = f} := by rw [hfib]; norm_num
    obtain ⟨⟨P, hP⟩⟩ := Nat.card_pos_iff.mp this |>.1
    exact ⟨P, hP⟩
  haveI : Finite (countSet H) := Finite.of_surjective g hsurj
  exact ⟨Set.toFinite _, card_eq_mul_of_fibres g 2 (by norm_num) hfib⟩

end Cyclic

/-! ### Cyclic and split points partition the integral points -/

theorem IP_union (H : ℝ) : IP H = IPc H ∪ IPs H := by
  ext P
  constructor
  · intro hP
    rcases QuotientCubicClassification.cyclic_or_splits P with h | h
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

theorem IP_disjoint (H : ℝ) : Disjoint (IPc H) (IPs H) := by
  rw [Set.disjoint_left]
  rintro P ⟨_, hc⟩ ⟨_, hs⟩
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (by
    rw [characteristicPolynomial, degree_eq_natDegree (CyclicCubicField.cubic_monic _ _).ne_zero,
      CyclicCubicField.cubic_natDegree]; decide)
  exact CyclicCubicField.not_isRoot_of_cyclic _ _ hc r hr

/-- The exact count before estimating the ellipse contribution. -/
theorem exact_count : CubicTargets.Counting.WeightedPolynomialCount.ExactClaim := by
  intro H hH
  obtain ⟨hfin, hcyc⟩ := card_cyclic H hH
  refine ⟨hfin, ?_⟩
  have hsplit := card_split H hH
  have hsum := sum_count_eq H
  have hunion : Nat.card (IP H) = Nat.card (IPc H) + Nat.card (IPs H) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, IP_union,
      Set.ncard_union_eq (IP_disjoint H) ((IP_finite H).subset fun P hP => hP.1)
        (IPs_finite H hH)]
  have hsumR : (∑ n ∈ Finset.Icc 1 ⌊H ^ 2⌋₊,
      (Cubic.PoissonSummation.HeightCountingData.count n : ℝ)) = Nat.card (IP H) := by
    exact_mod_cast hsum
  rw [hsumR]
  have e1 : (Nat.card (IP H) : ℝ) = Nat.card (IPc H) + Nat.card (IPs H) := by exact_mod_cast hunion
  have e2 : (Nat.card (IPc H) : ℝ) = Nat.card (CubicTargets.Counting.WeightedPolynomialCount.countSet H) * 2 := by
    exact_mod_cast hcyc
  have e3 : (Nat.card (latticePoints H) : ℝ) = Nat.card (IPs H) * 3 := by exact_mod_cast hsplit
  rw [e1, e2, e3]
  ring

/-- `eqn:weightedPolynomialCount`, in the current variable `X = H²`. -/
theorem «eqn:weightedPolynomialCount» : CubicTargets.Counting.WeightedPolynomialCount.Claim := by
  have hs : ∀ X : ℝ, 1 ≤ X → 1 ≤ Real.sqrt X := fun X hX => by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    simpa using hX
  refine ⟨fun X hX => (exact_count _ (hs X hX)).1, ?_⟩
  obtain ⟨K, hK⟩ := EllipseLatticeCount.«eqn:ellipseLatticeCount» |>.2
  refine ⟨K / 6, fun X hX => ?_⟩
  have hsq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt (by linarith)
  have hw := (exact_count _ (hs X hX)).2
  have he := hK _ (hs X hX)
  rw [hsq] at hw he
  rw [hw]
  have hid : (1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      (Cubic.PoissonSummation.HeightCountingData.count n : ℝ)) -
      (1 / 6) * Nat.card (latticePoints (Real.sqrt X)) -
      ((1 / 2) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (Cubic.PoissonSummation.HeightCountingData.count n : ℝ)) -
          Real.pi / (9 * Real.sqrt 3) * X) =
      -(1 / 6 : ℝ) * ((Nat.card (latticePoints (Real.sqrt X)) : ℝ) -
        2 * Real.pi / (3 * Real.sqrt 3) * X) := by ring
  rw [hid, abs_mul]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  linarith

end Cubic.Counting.WeightedCount
