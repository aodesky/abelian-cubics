import Cubic.Counting.AsymptoticPolynomialCount
import Cubic.PoissonSummation.HeightZetaCountingFormula
import CubicTargets.Counting.ExactFormula
import Cubic.Counting.PrimaryNormCount
import Cubic.Counting.PrimePowerIdealCount
import Cubic.PoissonSummation.HeightCoefficients

/-!
# Proof of `thm:exactFormula`

The paper: "Since the roots of every `f ∈ F` are normal, Proposition
`prop:canonicalHeight` shows that every `f ∈ F` arises from an integral point of `T`.
Lemma `lemma:rootVsToric` therefore gives `a ≤ 0`. Now fix `a ∈ ℤ_{≤0}` and put
`n = 1−3a`, so that `3 ∤ n`. The split points of height `√n` are represented by triples
`(x,y,z) ∈ ℤ³` with `x+y+z = 1` and `xy+yz+zx = a`, modulo cyclic permutation. To such a
triple attach `θ = x+yζ+zζ² ∈ 𝓞_E`. Then `Nθ = (x+y+z)² − 3(xy+yz+zx) = n` and
`θ ≡ x+y+z = 1 (mod 1−ζ)`. Conversely, if `θ = u+vζ` satisfies `θ ≡ 1 (mod 1−ζ)`, that
is, `u+v ≡ 1 (mod 3)`, then `θ` comes from exactly one triple, namely `z = (1−u−v)/3`,
`x = u+z`, `y = v+z`. Cyclically permuting the triple multiplies `θ` by a power of `ζ`.
Since `3 ∤ n`, an ideal of norm `n` has six generators `±ζʲθ`, and since
`ζ ≡ 1 (mod 1−ζ)`, exactly three of them, `θ, ζθ, ζ²θ`, are congruent to `1`. Hence the
split points of height `√n` correspond bijectively to the ideals of norm `n`, and there
are `a_E(n)` of them. Each irreducible polynomial contributes two points; hence their
number is `½(d_n − a_E(n))`.

It remains to show that `d_n = a_E(n³)`. An ideal of norm `p^{3k}` with `p ≡ 1 (mod 3)` is
`𝔭^i 𝔭̄^{3k−i}` for some `0 ≤ i ≤ 3k`, which gives `3k+1` choices. An ideal of norm
`q^{3k}` with `q ≡ 2 (mod 3)` exists only if `3k` is even, that is, `k` is even, and is
then unique. Comparing with Remark `rem:heightCoefficients` gives `d_n = a_E(n³)`."

The bijection is `splitIdealEquiv`. The split points are the triples modulo the relation
`pointOf v = pointOf w`, which is cyclic permutation (`pointOf_surjective`,
`pointOf_eq_iff`). The triple gives `θ` (`theta`, `residue_theta`, `norm_theta`), and
`tripleEquiv` (in the coordinates `θ = (x−z) + (y−z)ζ`, `theta_eq_coord`) with
`theta_injective` is the converse. `theta_shift` says a cyclic permutation multiplies `θ`
by a power of `ζ`, and `PrimaryNormCount.primary_generator_iff` says the generators of
`(θ)` congruent to `1` are `θ, ζθ, ζ²θ`; together they show that two triples give the same
ideal `(θ)` exactly when they are cyclic permutations of each other (`idealOf_eq_iff`).
Every ideal of norm `n` arises (`idealOf_surjective`, via
`PrimaryNormCount.exists_primary_generator`). So both maps identify the same quotient of
the triples, with the split points and with the ideals of norm `n`.

For `d_n = a_E(n³)` (`aE_cube`): `a_E` is multiplicative on coprime arguments
(`PrimePowerIdealCount.aE_mul`), so `a_E(n³) = ∏_{p^k ∥ n} a_E(p^{3k})`. Since `3 ∤ n`,
each `p` is split or inert; `PrimePowerIdealCount.aE_split` (`𝔭^i 𝔭̄^{m−i}`, `m+1`
choices) and `PrimePowerIdealCount.aE_inert` (`(q)^{m/2}` when `m` is even, none
otherwise) give the local factors, and the product is the formula for `d_n` in
`rem:heightCoefficients`.
-/

noncomputable section

namespace Cubic.Counting.ExactFormula

open Polynomial Cubic.Counting.PolynomialCountData Cubic.Counting.WeightedCount
open Cubic.Counting.SplitPoints Cubic.Counting.SplitCount
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open CubicTargets.Counting.ExactFormula (fibre normIdeals aE)

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

/-- A triple's split point. -/
def pointOf (v : exactTriples a) : IPs a := ⟨triplePoint v.val, triplePoint_mem_IPs v.val v.property⟩

/-- The split points of height `√n` are represented by triples with `xy+yz+zx = a`. -/
theorem pointOf_surjective : Function.Surjective (pointOf (a := a)) := by
  rintro ⟨P, hP⟩
  rw [← image_exact] at hP
  obtain ⟨v, hv, rfl⟩ := hP
  exact ⟨⟨v, hv⟩, rfl⟩

/-- Two triples represent the same split point exactly when they differ by a cyclic
permutation. -/
theorem pointOf_eq_iff (v w : exactTriples a) :
    pointOf v = pointOf w ↔ ∃ c : ZMod 3, w.val = shift c v.val := by
  rw [Subtype.ext_iff]
  change triplePoint v.val = triplePoint w.val ↔ _
  rw [triplePoint_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext (funext hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun h => by rw [hc]; rfl⟩

/-! ### The element `θ = x + yζ + zζ²` of a triple -/

open Cubic.PoissonSummation.CyclotomicIntegerUnits Cubic.Counting.EisensteinNormCount
  Cubic.Counting.PrimaryNormCount

/-- `θ = x + yζ + zζ² ∈ 𝓞_E` attached to the triple `(x, y, z)`. -/
def theta (v : Triple) : Integers :=
  v.val 0 + v.val 1 * zetaInteger + v.val 2 * zetaInteger ^ 2

/-- `θ = x + yζ + zζ² = (x−z) + (y−z)ζ`, since `ζ² = −1−ζ`. -/
theorem theta_eq_coord (v : Triple) : theta v = coord (v.val 0 - v.val 2, v.val 1 - v.val 2) := by
  rw [theta, coord, zetaInteger_sq]
  push_cast
  ring

/-- `θ ≡ x + y + z = 1 (mod 1−ζ)`, since `ζ ≡ 1`. -/
theorem residue_theta (v : Triple) : residue (theta v) = 1 := by
  have h := congrArg (Int.cast : ℤ → ZMod 3) v.property
  push_cast at h
  simp only [theta, map_add, map_mul, map_pow, map_intCast, residue_zeta, one_pow, mul_one]
  exact h

/-- `θ` in the coordinates `θ = u + vζ = (x−z) + (y−z)ζ` (`theta_eq_coord`): it has
`Nθ = u² − uv + v² = n` and `u + v ≡ 1 (mod 3)`, that is `θ ≡ 1 (mod 1−ζ)`
(`PrimaryNormCount.dvd_iff_residue`). Conversely, if `θ = u + vζ` satisfies these, it comes
from the triple `z = (1−u−v)/3`, `x = u + z`, `y = v + z`, and from no other. -/
def tripleEquiv (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) :
    exactTriples a ≃ PrimaryNormCount.primarySet n where
  toFun v := ⟨(v.val.val 0 - v.val.val 2, v.val.val 1 - v.val.val 2), by
    have hs := v.val.property
    have hv : Cubic.OrbitParametrization.secondCoeff (v.val.val 0) (v.val.val 1)
        (v.val.val 2) = a := v.property
    simp only [Cubic.OrbitParametrization.secondCoeff] at hv
    refine ⟨?_, ⟨v.val.val 2, ?_⟩⟩
    · linear_combination (v.val.val 0 + v.val.val 1 + v.val.val 2 + 1) * hs - 3 * hv - hn
    · linear_combination -hs⟩
  invFun p := by
    refine ⟨ofPair (p.1.1 + (1 - p.1.1 - p.1.2) / 3, p.1.2 + (1 - p.1.1 - p.1.2) / 3), ?_⟩
    obtain ⟨hN, k, hk⟩ := p.2
    have hz : (1 - p.1.1 - p.1.2) / 3 = k := by rw [hk]; omega
    obtain ⟨h0, h1, h2⟩ := ofPair_val (p.1.1 + (1 - p.1.1 - p.1.2) / 3,
      p.1.2 + (1 - p.1.1 - p.1.2) / 3)
    change Cubic.OrbitParametrization.secondCoeff _ _ _ = a
    rw [h0, h1, h2]
    simp only [Cubic.OrbitParametrization.secondCoeff, hz]
    have h3 : (3 : ℤ) * a = 1 - n := by omega
    have hz' : 1 - (p.1.1 + k) - (p.1.2 + k) = k := by linarith
    rw [hz']
    have : 3 * ((p.1.1 + k) * (p.1.2 + k) + (p.1.2 + k) * k + k * (p.1.1 + k)) = 3 * a := by
      linear_combination -hN - h3 - (p.1.1 + p.1.2 + 3 * k + 1) * hk
    omega
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    have hs := v.val.property
    have hz : (1 - (v.val.val 0 - v.val.val 2) - (v.val.val 1 - v.val.val 2)) / 3 =
        v.val.val 2 := by omega
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hi with rfl | rfl | rfl
    · change v.val.val 0 - v.val.val 2 + _ = _; rw [hz]; ring
    · change v.val.val 1 - v.val.val 2 + _ = _; rw [hz]; ring
    · change 1 - (v.val.val 0 - v.val.val 2 + _) - (v.val.val 1 - v.val.val 2 + _) = _
      rw [hz]; omega
  right_inv p := by
    obtain ⟨⟨u, w⟩, hN, k, hk⟩ := p
    apply Subtype.ext
    have hz : (1 - u - w) / 3 = k := by rw [hk]; omega
    change ((u + (1 - u - w) / 3) - (1 - (u + (1 - u - w) / 3) - (w + (1 - u - w) / 3)),
      (w + (1 - u - w) / 3) - (1 - (u + (1 - u - w) / 3) - (w + (1 - u - w) / 3))) = (u, w)
    rw [hz]
    ext <;> simp <;> omega

/-- `Nθ = (x+y+z)² − 3(xy+yz+zx) = n`. -/
theorem norm_theta (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) (v : exactTriples a) :
    Algebra.norm ℤ (theta v.val) = n := by
  rw [theta_eq_coord, norm_coord]
  exact (tripleEquiv n hn v).property.1

/-- The triple that `tripleEquiv` attaches to `u + vζ` has `θ = u + vζ`. -/
theorem theta_tripleEquiv_symm (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a)
    (p : PrimaryNormCount.primarySet n) : theta ((tripleEquiv n hn).symm p).val = coord p.val := by
  rw [theta_eq_coord]
  exact congrArg coord (congrArg Subtype.val ((tripleEquiv n hn).apply_symm_apply p))

/-- `θ` comes from exactly one triple. -/
theorem theta_injective : Function.Injective theta := by
  intro v w h
  rw [theta_eq_coord, theta_eq_coord] at h
  have h' := coord_injective h
  simp only [Prod.mk.injEq] at h'
  have hv := v.property
  have hw := w.property
  apply Subtype.ext
  funext i
  rcases (show ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) i with rfl | rfl | rfl <;> omega

/-- Cyclically permuting the triple multiplies `θ` by a power of `ζ`: the shift
`(x, y, z) ↦ (y, z, x)` multiplies `θ` by `ζ² = ζ⁻¹`. -/
theorem theta_shift (c : ZMod 3) (v : Triple) :
    theta (shift c v) = zetaInteger ^ (-c).val * theta v := by
  have h3 : zetaInteger ^ 3 = 1 := by
    rw [← coe_zetaUnit, ← Units.val_pow_eq_pow_val, zetaUnit_cube, Units.val_one]
  simp only [theta, shift]
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) c with rfl | rfl | rfl
  · simp
  · simp only [zero_add, show (1 : ZMod 3) + 1 = 2 by decide,
      show (2 : ZMod 3) + 1 = 0 by decide, show (-1 : ZMod 3).val = 2 from rfl]
    linear_combination (-(v.val 1 : Integers) - v.val 2 * zetaInteger) * h3
  · simp only [zero_add, show (1 : ZMod 3) + 2 = 0 by decide,
      show (2 : ZMod 3) + 2 = 1 by decide, show (-2 : ZMod 3).val = 1 from rfl]
    linear_combination (-(v.val 2 : Integers)) * h3

/-! ### The bijection between split points and ideals of norm `n` -/

/-- The ideal `(θ)` of norm `n` attached to a triple. -/
def idealOf (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) (v : exactTriples a) : normIdeals n :=
  ⟨Ideal.span {theta v.val}, by
    change Ideal.absNorm _ = n
    rw [Ideal.absNorm_span_singleton, norm_theta n hn v, Int.natAbs_natCast]⟩

/-- Every ideal of norm `n` is `(θ)` for a triple: since `3 ∤ n` it has a generator
`θ = u + vζ ≡ 1`, which comes from a triple. -/
theorem idealOf_surjective (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) (h3 : ¬ 3 ∣ n) :
    Function.Surjective (idealOf n hn) := by
  intro I
  obtain ⟨θ, hθI, hθ⟩ := exists_primary_generator ⟨I.1, I.2⟩ h3
  obtain ⟨p, rfl⟩ := coord_surjective θ
  have hp : p ∈ PrimaryNormCount.primarySet n := by
    refine ⟨?_, (dvd_iff_residue p).mpr hθ⟩
    have h : Ideal.absNorm I.1 = n := I.2
    rw [← hθI, Ideal.absNorm_span_singleton, norm_coord] at h
    rw [← Int.natAbs_of_nonneg (normForm_nonneg _ _), h]
  refine ⟨(tripleEquiv n hn).symm ⟨p, hp⟩, Subtype.ext ?_⟩
  change Ideal.span {theta _} = I.1
  rw [theta_tripleEquiv_symm, hθI]

/-- Two triples give the same ideal exactly when they differ by a cyclic permutation: the
generators of `(θ)` congruent to `1` are `θ, ζθ, ζ²θ`, and these are the `θ` of the
cyclic permutations of the triple. -/
theorem idealOf_eq_iff (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) (v w : exactTriples a) :
    idealOf n hn v = idealOf n hn w ↔ ∃ c : ZMod 3, w.val = shift c v.val := by
  rw [Subtype.ext_iff]
  change Ideal.span {theta v.val} = Ideal.span {theta w.val} ↔ _
  rw [eq_comm, primary_generator_iff (residue_theta _) (residue_theta _)]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨-j, theta_injective (by rw [hj, theta_shift, neg_neg])⟩
  · rintro ⟨c, hc⟩
    exact ⟨-c, by rw [hc, theta_shift]⟩

/-- The paper's bijection between the split points of height `√n` and the ideals of
norm `n`: split points are triples modulo cyclic permutation (`pointOf`), and a triple
modulo cyclic permutation is `θ` modulo `⟨ζ⟩`, which is the ideal `(θ)` (`idealOf`). -/
def splitIdealEquiv (n : ℕ) (hn : (n : ℤ) = 1 - 3 * a) (h3 : ¬ 3 ∣ n) :
    IPs a ≃ normIdeals n :=
  (Setoid.quotientKerEquivOfSurjective _ pointOf_surjective).symm.trans
    ((Quotient.congrRight fun v w =>
        (pointOf_eq_iff v w).trans (idealOf_eq_iff n hn v w).symm).trans
      (Setoid.quotientKerEquivOfSurjective _ (idealOf_surjective n hn h3)))

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

/-! ### `d_n = a_E(n³)` -/

/-- `a_E(n³)` for `3 ∤ n` is the product formula of `rem:heightCoefficients`: `3k+1` for
each `p^k ∥ n` with `p ≡ 1 (mod 3)`, and `0` unless every `q ≡ 2 (mod 3)` divides `n` to
an even power. -/
theorem aE_cube {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    (aE (n ^ 3) : ℤ) = if ∀ p ∈ n.primeFactors, p % 3 = 2 → Even (n.factorization p)
      then ∏ p ∈ n.primeFactors.filter (fun p => p % 3 = 1),
        (3 * (n.factorization p : ℤ) + 1) else 0 := by
  classical
  open PrimePowerIdealCount in
  -- `a_E` is multiplicative, so `a_E(n³) = ∏_{p^k ∥ n} a_E(p^{3k})`
  rw [Nat.multiplicative_factorization (fun m => (aE (m ^ 3) : ℤ))
    (fun x y hxy => by simp only [mul_pow, aE_mul (hxy.pow 3 3), Nat.cast_mul])
    (by simp [aE_one]) hn.ne']
  simp only [Finsupp.prod, Nat.support_factorization, ← pow_mul]
  -- `3 ∤ n`, so every prime factor of `n` is split or inert
  have hres : ∀ p ∈ n.primeFactors, p % 3 = 1 ∨ p % 3 = 2 := by
    intro p hp
    have hp3 : p ≠ 3 := fun he => h3 (he ▸ Nat.dvd_of_mem_primeFactors hp)
    have hnd : ¬ 3 ∣ p := fun h => hp3 (((Nat.prime_of_mem_primeFactors hp).dvd_iff_eq
      (by decide)).mp h)
    omega
  split_ifs with hall
  · rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    rcases hres p hp with hr | hr
    · -- `p ≡ 1`: `3k+1` ideals `𝔭^i 𝔭̄^{3k−i}`
      rw [if_pos hr, PrimePowerIdealCount.aE_split ⟨⟨p, hpr⟩, hr⟩]
      push_cast
      ring
    · -- `q ≡ 2` with `k` even: the unique ideal `(q)^{3k/2}`
      rw [if_neg (by omega), PrimePowerIdealCount.aE_inert ⟨⟨p, hpr⟩, hr⟩,
        if_pos ((hall p hp hr).mul_right 3), Nat.cast_one]
  · -- some `q ≡ 2` with `k` odd: no ideal of norm `q^{3k}`
    push_neg at hall
    obtain ⟨p, hp, hr, hk⟩ := hall
    refine Finset.prod_eq_zero hp ?_
    have hodd : ¬ Even (n.factorization p * 3) := by
      rw [Nat.even_mul]; exact fun h => h.elim hk (by decide)
    rw [PrimePowerIdealCount.aE_inert ⟨⟨p, Nat.prime_of_mem_primeFactors hp⟩, hr⟩,
      if_neg hodd, Nat.cast_zero]

/-- `thm:exactFormula`, relative to the Poisson summation input
`PoissonWithDualMeasure.BlackBox`, which enters through `rem:heightCoefficients`
(the product formula for `d_n`). -/
theorem «thm:exactFormula»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.Counting.ExactFormula.Claim := by
  refine ⟨a_nonpos, fun a ha => ?_⟩
  set n : ℕ := (1 - 3 * a).toNat with hndef
  have hn : (n : ℤ) = 1 - 3 * a := Int.toNat_of_nonneg (by omega)
  have hn0 : 0 < n := by omega
  have hn3 : ¬ 3 ∣ n := by omega
  obtain ⟨hfin, hcyc⟩ := card_cyclic n hn
  refine ⟨hfin, Ideal.finite_setOf_absNorm_eq n, Ideal.finite_setOf_absNorm_eq (n ^ 3), ?_⟩
  -- the split points of height `√n` correspond bijectively to the ideals of norm `n`
  have hs : Nat.card (IPs a) = aE n := Nat.card_congr (splitIdealEquiv n hn hn3)
  -- `d_n = a_E(n³)`: compare `aE_cube` with `rem:heightCoefficients`
  have hd := (Cubic.PoissonSummation.HeightCoefficients.«rem:heightCoefficients» hPoisson).2.2
    n hn0 hn3
  rw [count_eq n hn, ← aE_cube hn0 hn3] at hd
  have hdn : (Nat.card (IPa a) : ℝ) = aE (n ^ 3) := by exact_mod_cast hd
  have hunion : Nat.card (IPa a) = Nat.card (IPc a) + Nat.card (IPs a) := by
    have hfa := IPa_finite n hn
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, IPa_union,
      Set.ncard_union_eq IPa_disjoint (hfa.subset fun P (hP : P ∈ IPc a) => hP.1)
        (hfa.subset fun P (hP : P ∈ IPs a) => hP.1)]
  have e1 : (Nat.card (IPa a) : ℝ) = Nat.card (IPc a) + Nat.card (IPs a) := by
    exact_mod_cast hunion
  have e2 : (Nat.card (IPc a) : ℝ) = Nat.card (fibre a) * 2 := by exact_mod_cast hcyc
  have e3 : (Nat.card (IPs a) : ℝ) = aE n := by exact_mod_cast hs
  rw [← hdn, e1, e2, e3]
  ring

end Cubic.Counting.ExactFormula
