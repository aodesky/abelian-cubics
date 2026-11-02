import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Cubic characters of `(ℤ/N)ˣ`

Supporting construction for `thm:lower` of `box_height_research_note.tex`. Fix a finite set
`S` of primes `p ≡ 1 (mod 3)`, and let the moduli be `9` and the `p ∈ S`; they are pairwise
coprime and `N` is their product. Each `(ℤ/q)ˣ` is cyclic of order divisible by `3`, so it has
a surjection `θ_q` onto `ℤ/3`. For `a : moduli → ℤ/3` put
`φ_a(u) = Σ_q a_q θ_q(u mod q)`. By the Chinese remainder theorem `u ↦ (θ_q(u mod q))_q` is
onto `(ℤ/3)^{moduli}`, so for `a ≠ 0` the character `φ_a` is onto, and `ker φ_a = ker φ_b`
forces `b = ±a`. If `u ≡ 1` modulo `c_a = ∏_{a_q ≠ 0} q`, then `φ_a(u) = 0`.
-/

noncomputable section

namespace Cubic.BoxHeight.CyclicCubicCharacters

/-- A finite set of primes `p ≡ 1 (mod 3)`. -/
structure SplitSet where
  S : Finset ℕ
  prime : ∀ p ∈ S, p.Prime
  mod_three : ∀ p ∈ S, p % 3 = 1

variable (P : SplitSet)

/-- The moduli: `none ↦ 9`, `some p ↦ p`. -/
abbrev ι := Option P.S

/-- The modulus attached to an index. -/
def q : ι P → ℕ
  | none => 9
  | some p => p.1

theorem q_pos (i : ι P) : 0 < q P i := by
  cases i with
  | none => norm_num [q]
  | some p => exact (P.prime p.1 p.2).pos

instance (i : ι P) : NeZero (q P i) := ⟨(q_pos P i).ne'⟩

theorem coprime_q : Pairwise (Function.onFun Nat.Coprime (q P)) := by
  intro i j hij
  have h9 : ∀ p : P.S, Nat.Coprime 9 p.1 := fun p => by
    have hp := P.prime p.1 p.2
    have h3 : ¬ 3 ∣ p.1 := fun h => by have := P.mod_three p.1 p.2; omega
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_three hp).mpr
      (fun he => h3 (he ▸ dvd_refl 3)))
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some p => exact h9 p
  | some p =>
    cases j with
    | none => exact (h9 p).symm
    | some p' =>
      have hne : p.1 ≠ p'.1 := fun h => hij (congrArg some (Subtype.ext h))
      exact (Nat.coprime_primes (P.prime p.1 p.2) (P.prime p'.1 p'.2)).mpr hne

/-- `N = 9 ∏_{p ∈ S} p`. -/
def N : ℕ := ∏ i, q P i

instance : NeZero (N P) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (q_pos P i).ne'⟩

theorem q_dvd_N (i : ι P) : q P i ∣ N P := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- `3` divides the order of `(ℤ/q)ˣ`. -/
theorem three_dvd_card (i : ι P) : 3 ∣ Nat.card (ZMod (q P i))ˣ := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  cases i with
  | none =>
    show 3 ∣ Nat.totient 9
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.totient_prime_pow Nat.prime_three (by norm_num)]
    norm_num
  | some p =>
    simp only [q]
    rw [Nat.totient_prime (P.prime p.1 p.2)]
    have := P.mod_three p.1 p.2
    exact (Nat.modEq_iff_dvd' (by have := (P.prime p.1 p.2).one_lt; omega)).mp
      (by unfold Nat.ModEq; omega)

theorem isCyclic_units (i : ι P) : IsCyclic (ZMod (q P i))ˣ := by
  cases i with
  | none =>
    simpa [q] using ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by norm_num) 2
  | some p =>
    haveI : Fact p.1.Prime := ⟨P.prime p.1 p.2⟩
    exact ZMod.isCyclic_units_prime (P.prime p.1 p.2)

/-- A surjection `θ_q : (ℤ/q)ˣ → ℤ/3`, written additively. -/
def θ (i : ι P) : (ZMod (q P i))ˣ →* Multiplicative (ZMod 3) :=
  (AddMonoidHom.toMultiplicative
      (ZMod.castHom (three_dvd_card P i) (ZMod 3)).toAddMonoidHom).comp
    (zmodCyclicMulEquiv (isCyclic_units P i)).symm.toMonoidHom

theorem θ_surjective (i : ι P) : Function.Surjective (θ P i) := by
  intro t
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (three_dvd_card P i) (Multiplicative.toAdd t)
  refine ⟨zmodCyclicMulEquiv (isCyclic_units P i) (Multiplicative.ofAdd x), ?_⟩
  simp only [θ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, AddMonoidHom.toMultiplicative_apply_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, toAdd_ofAdd]
  rw [hx, ofAdd_toAdd]

/-- The `q`-component `θ_q(u mod q) ∈ ℤ/3`. -/
def comp (i : ι P) (u : (ZMod (N P))ˣ) : ZMod 3 :=
  Multiplicative.toAdd (θ P i (ZMod.unitsMap (q_dvd_N P i) u))

theorem comp_mul (i : ι P) (u v : (ZMod (N P))ˣ) :
    comp P i (u * v) = comp P i u + comp P i v := by
  simp only [comp, map_mul, toAdd_mul]

theorem comp_one (i : ι P) : comp P i 1 = 0 := by simp [comp]

/-- The component maps of the Chinese remainder isomorphism are the reductions. -/
theorem prodEquivPi_apply (x : ZMod (N P)) (i : ι P) :
    ZMod.prodEquivPi (q P) (coprime_q P) x i = ZMod.castHom (q_dvd_N P i) (ZMod (q P i)) x := by
  have : (Pi.evalRingHom (fun j => ZMod (q P j)) i).comp
      (ZMod.prodEquivPi (q P) (coprime_q P)).toRingHom =
      ZMod.castHom (q_dvd_N P i) (ZMod (q P i)) := Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (N P) →+* ZMod (q P i) => f x) this

/-- Chinese remainder theorem for units. -/
theorem exists_units (t : ∀ i : ι P, (ZMod (q P i))ˣ) :
    ∃ u : (ZMod (N P))ˣ, ∀ i, ZMod.unitsMap (q_dvd_N P i) u = t i := by
  set e := ZMod.prodEquivPi (q P) (coprime_q P)
  set x : ZMod (N P) := e.symm (fun i => (t i : ZMod (q P i)))
  have hx : IsUnit x := (Pi.isUnit_iff.mpr fun i => (t i).isUnit).map e.symm
  refine ⟨hx.unit, fun i => Units.ext ?_⟩
  rw [ZMod.unitsMap_def, Units.coe_map, IsUnit.unit_spec]
  change ZMod.castHom (q_dvd_N P i) (ZMod (q P i)) x = t i
  rw [← prodEquivPi_apply]
  simp only [x, e, RingEquiv.apply_symm_apply]

/-- The components are jointly onto `(ℤ/3)^{moduli}`. -/
theorem comp_surjective (v : ι P → ZMod 3) : ∃ u : (ZMod (N P))ˣ, ∀ i, comp P i u = v i := by
  choose t ht using fun i => θ_surjective P i (Multiplicative.ofAdd (v i))
  obtain ⟨u, hu⟩ := exists_units P t
  exact ⟨u, fun i => by simp only [comp, hu, ht, toAdd_ofAdd]⟩

/-- `φ_a(u) = Σ_q a_q θ_q(u mod q)`. -/
def φ (a : ι P → ZMod 3) : (ZMod (N P))ˣ →* Multiplicative (ZMod 3) where
  toFun u := Multiplicative.ofAdd (∑ i, a i * comp P i u)
  map_one' := by simp [comp_one]
  map_mul' u v := by
    simp only [comp_mul, mul_add, Finset.sum_add_distrib, ofAdd_add]

theorem φ_eq_one_iff (a : ι P → ZMod 3) (u : (ZMod (N P))ˣ) :
    φ P a u = 1 ↔ ∑ i, a i * comp P i u = 0 := by
  simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
  exact ofAdd_eq_one

theorem φ_surjective {a : ι P → ZMod 3} (ha : a ≠ 0) : Function.Surjective (φ P a) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  intro t
  obtain ⟨u, hu⟩ := comp_surjective P (Pi.single i ((a i)⁻¹ * Multiplicative.toAdd t))
  refine ⟨u, ?_⟩
  simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, hu]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, ← mul_assoc,
    mul_inv_cancel₀ hi, one_mul, ofAdd_toAdd]

theorem mul_self_of_ne_zero : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

theorem eq_one_or_neg_one : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide

/-- Two nonzero functionals on `(ℤ/3)^ι` with the same kernel differ by a sign. -/
theorem eq_or_eq_neg_of_ker {a b : ι P → ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : ι P → ZMod 3, ∑ i, a i * v i = 0 ↔ ∑ i, b i * v i = 0) : b = a ∨ b = -a := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hprop : ∀ j, b j = (b i * a i) * a j := by
    intro j
    by_cases hij : j = i
    · subst hij
      have : a j * a j = 1 := mul_self_of_ne_zero _ hi
      rw [mul_assoc, this, mul_one]
    · set v : ι P → ZMod 3 := Pi.single j (a i) - Pi.single i (a j)
      have hsum : ∀ c : ι P → ZMod 3, ∑ k, c k * v k = c j * a i - c i * a j := by
        intro c
        simp only [v, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
            (fun h => absurd (Finset.mem_univ j) h),
          Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
            (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, Pi.single_eq_same]
      have h1 := (h v).mp (by rw [hsum]; ring)
      rw [hsum] at h1
      have hai : a i * a i = 1 := mul_self_of_ne_zero _ hi
      linear_combination a i * h1 - b j * hai
  set l := b i * a i
  have hl : l ≠ 0 := by
    intro hl0
    exact hb (funext fun j => by rw [hprop j, hl0, zero_mul, Pi.zero_apply])
  have hl' : l = 1 ∨ l = -1 := eq_one_or_neg_one l hl
  rcases hl' with hl1 | hl1
  · left; funext j; rw [hprop j, hl1, one_mul]
  · right; funext j; rw [hprop j, hl1, Pi.neg_apply, neg_one_mul]

theorem eq_or_eq_neg_of_ker_eq {a b : ι P → ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (φ P a).ker = (φ P b).ker) : b = a ∨ b = -a := by
  refine eq_or_eq_neg_of_ker P ha hb fun v => ?_
  obtain ⟨u, hu⟩ := comp_surjective P v
  have := congrArg (fun H : Subgroup (ZMod (N P))ˣ => u ∈ H) h
  simp only [MonoidHom.mem_ker, φ_eq_one_iff, hu, eq_iff_iff] at this
  exact this

theorem ker_neg (a : ι P → ZMod 3) : (φ P (-a)).ker = (φ P a).ker := by
  ext u
  simp only [MonoidHom.mem_ker, φ_eq_one_iff, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
    neg_eq_zero]

/-- The support of `a` and the conductor `c_a = ∏_{a_q ≠ 0} q`. -/
def supp (a : ι P → ZMod 3) : Finset (ι P) := Finset.univ.filter fun i => a i ≠ 0

def cond (a : ι P → ZMod 3) : ℕ := ∏ i ∈ supp P a, q P i

theorem cond_dvd_N (a : ι P → ZMod 3) : cond P a ∣ N P :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

theorem cond_pos (a : ι P → ZMod 3) : 0 < cond P a :=
  Finset.prod_pos fun i _ => q_pos P i

theorem cond_neg (a : ι P → ZMod 3) : cond P (-a) = cond P a := by
  simp [cond, supp]

/-- If `u ≡ 1 (mod c_a)`, then `φ_a(u) = 1`. -/
theorem φ_eq_one_of_cast {a : ι P → ZMod 3} {u : (ZMod (N P))ˣ}
    (hu : ZMod.castHom (cond_dvd_N P a) (ZMod (cond P a)) (u : ZMod (N P)) = 1) :
    φ P a u = 1 := by
  rw [φ_eq_one_iff]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : a i = 0
  · rw [hi, zero_mul]
  · have hdvd : q P i ∣ cond P a :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    have h1 : ZMod.unitsMap (q_dvd_N P i) u = 1 := by
      refine Units.ext ?_
      rw [ZMod.unitsMap_def, Units.coe_map, Units.val_one]
      have hc := congrArg (ZMod.castHom hdvd (ZMod (q P i))) hu
      rw [map_one, ← RingHom.comp_apply,
        show (ZMod.castHom hdvd (ZMod (q P i))).comp
          (ZMod.castHom (cond_dvd_N P a) (ZMod (cond P a))) =
          ZMod.castHom (q_dvd_N P i) (ZMod (q P i)) from Subsingleton.elim _ _] at hc
      exact hc
    simp only [comp, h1, map_one, toAdd_one, mul_zero]

end Cubic.BoxHeight.CyclicCubicCharacters
