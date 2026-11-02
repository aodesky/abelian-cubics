import Cubic.Counting.AsymptoticPolynomialCount
import Cubic.PoissonSummation.HeightZetaCountingFormula
import CubicTargets.Counting.ExactFormula

/-!
# Proof of `thm:exactFormula`

The paper: "By Corollary `cor:automaticallyNormal` and Proposition `prop:canonicalHeight`,
every `f ∈ F` arises from a `D₀`-integral point of `T`. Lemma `lemma:rootVsToric`
therefore gives `a ≤ 0`. Fix such an integer `a` and put `n = 1−3a`. The same free
`C₃`-action used above identifies split points of height exactly `√n` with orbits of
`E_{√n}(ℤ)`, so there are `⅓ #E_{√n}(ℤ)` such points. Each irreducible polynomial
contributes two points; hence their number is `½ d_n − ⅙ #E_{√n}(ℤ)`. Since `3 ∤ n`,
Theorem `thm:heightZetaFunctionFormula` supplies the stated divisor sum for `d_n`."

This is the exact-height version of `eqn:weightedPolynomialCount` (`WeightedCount`). As
there, every `f ∈ F` arises from an integral point by `thm:modularInterpretation`
(`AsymptoticPolynomialCount.exists_point`).
-/

noncomputable section

namespace Cubic.Counting.ExactFormula

open Polynomial Cubic.Counting.PolynomialCountData Cubic.Counting.WeightedCount
open Cubic.Counting.SplitPoints Cubic.Counting.SplitCount
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open CubicTargets.Counting.ExactFormula (ellipsePoints fibre divisorSum)

/-- `lemma:rootVsToric`: if `t³−t²+at+b ∈ F` then `a ≤ 0`. -/
theorem a_nonpos (a b : ℤ) (h : traceOneCubic a b ∈ cyclicPolynomials) : a ≤ 0 := by
  have hc := h.2
  rw [traceOneCubic_map] at hc
  obtain ⟨Q, -, ha⟩ := AsymptoticPolynomialCount.exists_point a b hc
  have hl := (Cubic.ToricHeights.«lemma:rootVsToric» Q).linear_nonpos
  rw [Cubic.ToricHeights.IntegralPolynomialData.linear, ha, Rat.num_intCast] at hl
  exact hl

section Fixed

variable (a : ℤ)

/-- Integral points with linear coefficient `a`, i.e. of toric height `√(1−3a)`. -/
def IPa : Set Pts :=
  {P | Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P ∧ P linearCoefficient = a}

def IPs : Set Pts := {P | P ∈ IPa a ∧ (characteristicPolynomial P).Splits}

def IPc : Set Pts := {P | P ∈ IPa a ∧ HasCyclicCubicGaloisGroup (characteristicPolynomial P)}

variable {a}

/-! ### `d_n` counts the integral points with linear coefficient `a` -/

open Cubic.PoissonSummation Cubic.PoissonSummation.AdelicHeightZetaData
  Cubic.PoissonSummation.IntegralHeightIndex Cubic.PoissonSummation.HeightCountingSeries in
/-- Integral points of index `n = 1−3a` are the integral points with linear coefficient `a`. -/
def indexEquiv (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) : IndexFiber n ≃ IPa a where
  toFun Q := ⟨Q.val.val, (IntegralPointComparison.integralPoint_iff _).mpr Q.val.property, by
    have h := index_cast Q.val
    rw [Q.property, hn] at h
    rw [Rat.eq_num_of_isInt (linear_isInt Q.val)]
    exact_mod_cast (by omega : (Q.val.val linearCoefficient).num = a)⟩
  invFun P := ⟨⟨P.val, (IntegralPointComparison.integralPoint_iff _).mp P.property.1⟩, by
    have h := index_cast ⟨P.val, (IntegralPointComparison.integralPoint_iff _).mp P.property.1⟩
    change (index _ : ℤ) = 1 - 3 * (P.val linearCoefficient).num at h
    have hlin : (P.val linearCoefficient).num = a := by rw [P.property.2, Rat.num_intCast]
    rw [hlin, ← hn] at h
    exact_mod_cast h⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Cubic.PoissonSummation in
theorem count_eq (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) :
    HeightCountingData.count n = Nat.card (IPa a) := by
  rw [HeightCountingData.count, Nat.card_congr (heightFibreEquiv n),
    Nat.card_congr (indexEquiv n hn)]

theorem IPa_finite (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) : (IPa a).Finite := by
  haveI := Cubic.PoissonSummation.HeightCountingSeries.index_fiber_finite n
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (indexEquiv n hn))

/-! ### Split points of height `√n` are the orbits of `E_{√n}(ℤ)` -/

/-- Triples `(α, β, γ)` with `αβ + βγ + γα = a`. -/
def exactTriples (a : ℤ) : Set Triple :=
  {v | Cubic.OrbitParametrization.secondCoeff (v.val 0) (v.val 1) (v.val 2) = a}

theorem curve_iff (ha : a ≤ 0) (α β : ℤ) :
    (α : ℝ) ^ 2 + (β : ℝ) ^ 2 + α * β - α - β = (Real.sqrt (1 - 3 * a) ^ 2 - 1) / 3 ↔
      Cubic.OrbitParametrization.secondCoeff α β (1 - α - β) = a := by
  have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  rw [Real.sq_sqrt (by linarith)]
  have h' := congrArg (Int.cast : ℤ → ℝ) (neg_secondCoeff α β)
  push_cast at h'
  constructor
  · intro h
    have : ((Cubic.OrbitParametrization.secondCoeff α β (1 - α - β) : ℤ) : ℝ) = a := by linarith
    exact_mod_cast this
  · intro h
    rw [h] at h'
    linarith

/-- `E_{√(1−3a)}(ℤ)` is the set of triples with `αβ + βγ + γα = a`. -/
def curveEquiv (ha : a ≤ 0) : ellipsePoints (Real.sqrt (1 - 3 * a)) ≃ exactTriples a where
  toFun p := ⟨ofPair p.val, (curve_iff ha _ _).mp p.property⟩
  invFun v := ⟨(v.val.val 0, v.val.val 1), by
    have hv : Cubic.OrbitParametrization.secondCoeff (v.val.val 0) (v.val.val 1)
        (v.val.val 2) = a := v.property
    have hsum := v.val.property
    rw [show v.val.val 2 = 1 - v.val.val 0 - v.val.val 1 by omega] at hv
    exact (curve_iff ha _ _).mpr hv⟩
  left_inv p := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hsum := v.val.property
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hi with rfl | rfl | rfl
    · rfl
    · rfl
    · change 1 - v.val.val 0 - v.val.val 1 = v.val.val 2
      omega

/-- The fibre of a triple's point in a shift-invariant set of triples is its orbit. -/
theorem fibre_card_of_invariant (S : Set Triple)
    (hS : ∀ c v, v ∈ S → shift c v ∈ S) (v : S) :
    Nat.card {w : S // triplePoint w.val = triplePoint v.val} = 3 := by
  have hset : {w : S | triplePoint w.val = triplePoint v.val} =
      Set.range (fun c : ZMod 3 => (⟨shift c v.val, hS c v.val v.property⟩ : S)) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hw
      obtain ⟨c, hc⟩ := (triplePoint_eq_iff v.val w.val).mp hw.symm
      exact ⟨c, Subtype.ext (Subtype.ext (funext fun h => (hc h).symm))⟩
    · rintro ⟨c, rfl⟩
      exact ((triplePoint_eq_iff v.val _).mpr ⟨c, fun h => rfl⟩).symm
  change Set.ncard {w : S | triplePoint w.val = triplePoint v.val} = 3
  rw [hset, Set.ncard_range_of_injective (fun c d hcd => shift_injective v.val
    (congrArg Subtype.val hcd))]
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem exact_invariant : ∀ c v, v ∈ exactTriples a → shift c v ∈ exactTriples a := by
  intro c v hv
  change Cubic.OrbitParametrization.secondCoeff _ _ _ = a
  rw [secondCoeff_shift]
  exact hv

theorem triplePoint_mem_IPs (v : Triple) (hv : v ∈ exactTriples a) : triplePoint v ∈ IPs a := by
  refine ⟨⟨triplePoint_integral v, ?_⟩, ?_⟩
  · rw [triplePoint_linear]
    exact_mod_cast hv
  · rw [triple_charPoly]
    exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

theorem image_exact : triplePoint '' exactTriples a = IPs a := by
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact triplePoint_mem_IPs v hv
  · rintro ⟨⟨hint, hlin⟩, hs⟩
    obtain ⟨v, rfl⟩ := exists_triple P hint hs
    refine ⟨v, ?_, rfl⟩
    rw [triplePoint_linear] at hlin
    change Cubic.OrbitParametrization.secondCoeff _ _ _ = a
    exact_mod_cast hlin

theorem card_split (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) :
    Nat.card (exactTriples a) = Nat.card (IPs a) * 3 := by
  haveI := ((IPa_finite n hn).subset fun P (hP : P ∈ IPs a) => hP.1).to_subtype
  let f : exactTriples a → IPs a := fun w => ⟨triplePoint w.val, triplePoint_mem_IPs w.val w.property⟩
  apply card_eq_mul_of_fibres f 3 (by norm_num)
  intro b
  have hb : b.val ∈ triplePoint '' exactTriples a := by rw [image_exact]; exact b.property
  obtain ⟨v, hv, hvb⟩ := hb
  rw [← fibre_card_of_invariant _ exact_invariant ⟨v, hv⟩]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro w
  simp only [f, Subtype.ext_iff, hvb]

/-! ### Each polynomial of `F` contributes two points -/

theorem constant_num {P : Pts} (hP : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P) :
    P constantCoefficient = ((P constantCoefficient).num : ℚ) := by
  obtain ⟨-, ⟨b, hb⟩⟩ :=
    (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P).mp hP
  rw [hb, Rat.num_intCast]

theorem mem_fibre (P : Pts) (hP : P ∈ IPc a) : (P constantCoefficient).num ∈ fibre a := by
  have hmap := toPoly_map P hP.1.1
  have htp : WeightedCount.toPoly P = traceOneCubic a (P constantCoefficient).num := by
    rw [WeightedCount.toPoly, hP.1.2, Rat.num_intCast]
  rw [htp] at hmap
  exact ⟨⟨_, _, rfl⟩, by rw [hmap]; exact hP.2⟩

/-- The points over `t³−t²+at+b ∈ F` are all the points with characteristic polynomial
`t³−t²+at+b`. -/
def cyclicFibreEquiv (b : ℤ) (hb : b ∈ fibre a) :
    {P : IPc a // (P.val constantCoefficient).num = b} ≃
      {P : Pts // characteristicPolynomial P = cubic a b} where
  toFun P := ⟨P.val.val, by
    rw [characteristicPolynomial, P.val.property.1.2, constant_num P.val.property.1.1,
      P.property]⟩
  invFun P := by
    have ha : P.val linearCoefficient = a := by
      have := congrArg (fun f : ℚ[X] => f.coeff 1) P.property
      simpa only [characteristicPolynomial, cubic_coeff_one] using this
    have hb' : P.val constantCoefficient = b := by
      have := congrArg (fun f : ℚ[X] => f.coeff 0) P.property
      simpa only [characteristicPolynomial, cubic_coeff_zero] using this
    have hint : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P.val :=
      (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P.val).mpr
        ⟨⟨a, ha⟩, ⟨b, hb'⟩⟩
    refine ⟨⟨P.val, ⟨hint, ha⟩, ?_⟩, ?_⟩
    · rw [P.property, ← traceOneCubic_map]; exact hb.2
    · rw [hb', Rat.num_intCast]
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cyclic (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) :
    (fibre a).Finite ∧ Nat.card (IPc a) = Nat.card (fibre a) * 2 := by
  haveI := ((IPa_finite n hn).subset fun P (hP : P ∈ IPc a) => hP.1).to_subtype
  let g : IPc a → fibre a := fun P => ⟨(P.val constantCoefficient).num, mem_fibre P.val P.property⟩
  have hfib : ∀ b : fibre a, Nat.card {P // g P = b} = 2 := by
    rintro ⟨b, hb⟩
    have hc := hb.2
    rw [traceOneCubic_map] at hc
    rw [← CyclicFibre.fibre_card _ _ hc, ← Nat.card_congr (cyclicFibreEquiv b hb)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro P
    simp only [g, Subtype.ext_iff]
  have hsurj : Function.Surjective g := fun b => by
    have : 0 < Nat.card {P // g P = b} := by rw [hfib]; norm_num
    obtain ⟨⟨P, hP⟩⟩ := (Nat.card_pos_iff.mp this).1
    exact ⟨P, hP⟩
  haveI : Finite (fibre a) := Finite.of_surjective g hsurj
  exact ⟨Set.toFinite _, card_eq_mul_of_fibres g 2 (by norm_num) hfib⟩

/-! ### Cyclic and split points partition the integral points of height `√n` -/

theorem IPa_union : IPa a = IPc a ∪ IPs a := by
  ext P
  constructor
  · intro hP
    rcases QuotientCubicClassification.cyclic_or_splits P with h | h
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

theorem IPa_disjoint : Disjoint (IPc a) (IPs a) := by
  rw [Set.disjoint_left]
  rintro P ⟨_, hc⟩ ⟨_, hs⟩
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (by
    rw [characteristicPolynomial, degree_eq_natDegree (CyclicCubicField.cubic_monic _ _).ne_zero,
      CyclicCubicField.cubic_natDegree]; decide)
  exact CyclicCubicField.not_isRoot_of_cyclic _ _ hc r hr

end Fixed

/-- `thm:exactFormula`, relative to the Poisson summation input `PoissonWithDualMeasure.BlackBox`, which enters through
`thm:heightZetaFunctionFormula` (the divisor sum for `d_n`). -/
theorem «thm:exactFormula»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.Counting.ExactFormula.Claim := by
  refine ⟨a_nonpos, fun a ha => ?_⟩
  set n : ℕ := (1 - 3 * a).toNat with hndef
  have hn : (n : ℤ) = 1 - 3 * a := Int.toNat_of_nonneg (by omega)
  have hn0 : 0 < n := by omega
  have hn3 : ¬ 3 ∣ n := by omega
  obtain ⟨hfin, hcyc⟩ := card_cyclic n hn
  have hsplit := card_split n hn
  have hcount := count_eq n hn
  have hS1 : 1 ≤ Real.sqrt (1 - 3 * a) := by
    have : (a : ℝ) ≤ 0 := by exact_mod_cast ha
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hEfin : (ellipsePoints (Real.sqrt (1 - 3 * a))).Finite :=
    ((Cubic.Counting.EllipseLatticeCount.«eqn:ellipseLatticeCount»).1 _ hS1).subset
      fun p hp => le_of_eq hp
  refine ⟨hfin, hEfin, ?_⟩
  have hE : Nat.card (ellipsePoints (Real.sqrt (1 - 3 * a))) = Nat.card (exactTriples a) :=
    Nat.card_congr (curveEquiv ha)
  have hunion : Nat.card (IPa a) = Nat.card (IPc a) + Nat.card (IPs a) := by
    have hfa := IPa_finite n hn
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, IPa_union,
      Set.ncard_union_eq IPa_disjoint (hfa.subset fun P (hP : P ∈ IPc a) => hP.1)
        (hfa.subset fun P (hP : P ∈ IPs a) => hP.1)]
  have hd := (Cubic.PoissonSummation.«thm:heightZetaFunctionFormula» hPoisson).point_count n hn0 hn3
  have hdiv : Cubic.PoissonSummation.HeightCountingData.divisorFormula n = divisorSum n := rfl
  rw [hdiv, hcount] at hd
  have hd' : ((Nat.card (IPa a) : ℤ) : ℝ) = (divisorSum n : ℝ) := by exact_mod_cast hd
  push_cast at hd'
  have e1 : (Nat.card (IPa a) : ℝ) = Nat.card (IPc a) + Nat.card (IPs a) := by
    exact_mod_cast hunion
  have e2 : (Nat.card (IPc a) : ℝ) = Nat.card (fibre a) * 2 := by exact_mod_cast hcyc
  have e3 : (Nat.card (ellipsePoints (Real.sqrt (1 - 3 * a))) : ℝ) = Nat.card (IPs a) * 3 := by
    rw [hE]; exact_mod_cast hsplit
  rw [e3, ← hd', e1, e2]
  ring

end Cubic.Counting.ExactFormula
