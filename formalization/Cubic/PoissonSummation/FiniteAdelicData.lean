import Cubic.PoissonSummation.QuotientFiniteFourierProduct
import Cubic.ToricHeights.QuotientFiniteRegularity
import Cubic.ToricHeights.RestrictedProductFunctions
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Finite adelic heights and logarithmic characters

Use the restricted product of the original quotient-point groups with respect
to their maximal compact subgroups. The local height and logarithm are the
residue-weighted constructions, independently of the Fourier factors. Compact
triviality makes the height product and logarithm sum finite at every point.

This is the finite-place construction only. The archimedean component,
rational diagonal and product formula, automorphic descent, and identification
are treated in other files.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteAdelicData

open Filter Function
open Cubic.ToricHeights
open QuotientFiniteHeight QuotientFiniteCompact QuotientFiniteRegularity
open CubicTargets.PoissonSummation.FiniteFourierProduct
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open LocalLogarithmNormalization
open scoped RestrictedProduct

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance splitFact (p : SplitPrimes) : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

/-- The weighted sum of the splitting-field place cocharacters above a rational prime. -/
def localLogarithm (p : Nat.Primes) : (family p).Carrier → ℝ × ℝ := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact splitLogarithm p
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inertLogarithm p
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact ramifiedLogarithm

theorem local_height_one (p : Nat.Primes) (s₀ σ : ℂ) :
    ∀ x ∈ (family p).maxCompact, (family p).inverseHeight s₀ σ x = 1 := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact split_height_one p s₀ σ
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inert_height_one p s₀ σ
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact ramified_height_one s₀ σ

theorem local_character_one (p : Nat.Primes) (t : ℝ) :
    ∀ x ∈ (family p).maxCompact, (family p).character t x = 1 := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact split_character_one p t
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inert_character_one p t
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact ramified_character_one t

private theorem transport_logarithm_property
    (P : (D : LocalData) → (D.Carrier → ℝ × ℝ) → Prop)
    {D F : LocalData} (h : D = F) (f : F.Carrier → ℝ × ℝ) (hf : P F f) :
    P D ((congrArg (fun D => D.Carrier → ℝ × ℝ) h).mpr f) := by
  subst F
  exact hf

/-- Eliminate the three prime cases while transporting both the point type and logarithm. -/
theorem localLogarithm_induction
    (P : (D : LocalData) → (D.Carrier → ℝ × ℝ) → Prop)
    (hsplit : ∀ p : SplitPrimes, P (splitData p) (splitLogarithm p.1))
    (hinert : ∀ p : InertPrimes, P (inertData p) (inertLogarithm p.1))
    (hthree : P ramifiedData ramifiedLogarithm) (p : Nat.Primes) :
    P (family p) (localLogarithm p) := by
  by_cases hs : (p : ℕ) % 3 = 1
  · simp only [localLogarithm, dif_pos hs]
    exact transport_logarithm_property P (family_split ⟨p, hs⟩) _ (hsplit ⟨p, hs⟩)
  by_cases hi : (p : ℕ) % 3 = 2
  · simp only [localLogarithm, dif_neg hs, dif_pos hi]
    exact transport_logarithm_property P (family_inert ⟨p, hi⟩) _ (hinert ⟨p, hi⟩)
  · simp only [localLogarithm, dif_neg hs, dif_neg hi]
    exact transport_logarithm_property P (by simp [family, hs, hi]) _ hthree

theorem local_logarithm_zero (p : Nat.Primes) :
    ∀ x ∈ (family p).maxCompact, localLogarithm p x = 0 :=
  localLogarithm_induction (fun D L => ∀ x ∈ D.maxCompact, L x = 0)
    (fun p => split_logarithm_zero p.1) (fun p => inert_logarithm_zero p.1)
    ramified_logarithm_zero p

theorem local_logarithm_mul (p : Nat.Primes) :
    ∀ x y, localLogarithm p (x * y) = localLogarithm p x + localLogarithm p y :=
  localLogarithm_induction (fun D L => ∀ x y : D.Carrier, L (x * y) = L x + L y)
    (fun p => split_logarithm_mul p.1) (fun p => inert_logarithm_mul p.1)
    ramified_logarithm_mul p

theorem local_character_formula (p : Nat.Primes) (t : ℝ) :
    ∀ x, (family p).character t x =
      Circle.exp (2 * Real.pi * spectralPairing t (localLogarithm p x)) :=
  localLogarithm_induction
    (fun D L => ∀ x, D.character t x = Circle.exp (2 * Real.pi * spectralPairing t (L x)))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) p

theorem continuous_localLogarithm (p : Nat.Primes) : Continuous (localLogarithm p) :=
  localLogarithm_induction (fun _ L => Continuous L)
    (fun p => continuous_splitLogarithm p.1) (fun p => continuous_inertLogarithm p.1)
    continuous_ramifiedLogarithm p

/-- The averaged place contribution lies in the Galois-invariant line. -/
theorem local_logarithm_invariant (p : Nat.Primes) :
    ∀ x, (localLogarithm p x).1 = (localLogarithm p x).2 := by
  apply localLogarithm_induction (fun _ L => ∀ x, (L x).1 = (L x).2)
  · intro p x
    rw [splitLogarithm_eq]
    simp only [conjugateAverage]
    ring
  · intro p x
    rw [inertLogarithm_eq, inert_rayCoordinates]
    rfl
  · intro x
    rw [ramifiedLogarithm_eq]
    rfl

theorem continuous_localInverseHeight (p : Nat.Primes) (s₀ σ : ℂ) :
    Continuous ((family p).inverseHeight s₀ σ) := by
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact continuous_splitInverseHeight p s₀ σ
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact continuous_inertInverseHeight p s₀ σ
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact continuous_ramifiedInverseHeight s₀ σ

/-- Finite adelic points of the original quotient, restricted at the maximal compacts. -/
abbrev Points := Πʳ p : Nat.Primes, [(family p).Carrier, (family p).maxCompact]

instance : Fact (∀ p : Nat.Primes, IsOpen ((family p).maxCompact : Set (family p).Carrier)) :=
  ⟨fun p => (family p).open_compact⟩

instance : IsTopologicalGroup Points := inferInstance

instance : LocallyCompactSpace Points :=
  RestrictedProduct.locallyCompactSpace_of_group (fun p => (family p).Carrier)
    (Filter.Eventually.of_forall fun p => (family p).compact)

/-- Finite-place inverse height, before the integrality cutoff. -/
def inverseHeight (s₀ σ : ℂ) (x : Points) : ℂ :=
  ∏' p : Nat.Primes, (family p).inverseHeight s₀ σ (x p)

/-- Finite-place part of the splitting-field weighted adelic logarithm. -/
def logarithm (x : Points) : ℝ × ℝ := ∑' p : Nat.Primes, localLogarithm p (x p)

theorem height_finite_mulSupport (s₀ σ : ℂ) (x : Points) :
    (mulSupport (fun p => (family p).inverseHeight s₀ σ (x p))).Finite :=
  RestrictedProductFunctions.finite_mulSupport _ (fun p => local_height_one p s₀ σ) x

theorem logarithm_finite_support (x : Points) :
    (support (fun p => localLogarithm p (x p))).Finite :=
  RestrictedProductFunctions.finite_support localLogarithm local_logarithm_zero x

theorem height_multipliable (s₀ σ : ℂ) (x : Points) :
    Multipliable (fun p => (family p).inverseHeight s₀ σ (x p)) :=
  multipliable_of_finite_mulSupport (height_finite_mulSupport s₀ σ x)

@[simp]
theorem inverseHeight_one (s₀ σ : ℂ) : inverseHeight s₀ σ 1 = 1 := by
  unfold inverseHeight
  trans ∏' _ : Nat.Primes, (1 : ℂ)
  · apply tprod_congr
    intro p
    exact local_height_one p s₀ σ 1 (family p).maxCompact.one_mem
  · exact tprod_one

theorem logarithm_summable (x : Points) : Summable (fun p => localLogarithm p (x p)) :=
  summable_of_finite_support (logarithm_finite_support x)

theorem continuous_inverseHeight (s₀ σ : ℂ) : Continuous (inverseHeight s₀ σ) :=
  RestrictedProductFunctions.continuous_tprod _ (fun p => local_height_one p s₀ σ)
    (fun p => continuous_localInverseHeight p s₀ σ)

theorem continuous_logarithm : Continuous logarithm :=
  RestrictedProductFunctions.continuous_tsum localLogarithm local_logarithm_zero
    continuous_localLogarithm

/-- The finite adelic logarithm takes values in the invariant real cocharacter line. -/
theorem logarithm_invariant (x : Points) : (logarithm x).1 = (logarithm x).2 := by
  change (ContinuousLinearMap.fst ℝ ℝ ℝ) (logarithm x) =
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (logarithm x)
  rw [logarithm, (ContinuousLinearMap.fst ℝ ℝ ℝ).map_tsum (logarithm_summable x),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).map_tsum (logarithm_summable x)]
  exact tsum_congr fun p => local_logarithm_invariant p (x p)

theorem logarithm_mul (x y : Points) : logarithm (x * y) = logarithm x + logarithm y := by
  simp only [logarithm, RestrictedProduct.mul_apply, local_logarithm_mul]
  exact (logarithm_summable x).tsum_add (logarithm_summable y)

@[simp]
theorem logarithm_one : logarithm 1 = 0 := by
  have h : ∀ p, localLogarithm p ((1 : Points) p) = 0 := by
    intro p
    exact local_logarithm_zero p 1 (family p).maxCompact.one_mem
  simp only [logarithm, h, tsum_zero]

/-- A finite set containing the noncompact components computes the height exactly. -/
theorem inverseHeight_eq_prod (s₀ σ : ℂ) (x : Points) (S : Finset Nat.Primes)
    (hS : ∀ p ∉ S, x p ∈ (family p).maxCompact) :
    inverseHeight s₀ σ x = ∏ p ∈ S, (family p).inverseHeight s₀ σ (x p) :=
  RestrictedProductFunctions.prod_eq_prod _ (fun p => local_height_one p s₀ σ) x S hS

theorem logarithm_eq_sum (x : Points) (S : Finset Nat.Primes)
    (hS : ∀ p ∉ S, x p ∈ (family p).maxCompact) :
    logarithm x = ∑ p ∈ S, localLogarithm p (x p) :=
  RestrictedProductFunctions.sum_eq_sum localLogarithm local_logarithm_zero x S hS

private theorem spectral_exp_add (t : ℝ) (u v : ℝ × ℝ) :
    Circle.exp (2 * Real.pi * spectralPairing t (u + v)) =
      Circle.exp (2 * Real.pi * spectralPairing t u) *
        Circle.exp (2 * Real.pi * spectralPairing t v) := by
  rw [← Circle.exp_add]
  congr 1
  simp only [spectralPairing, Prod.fst_add, Prod.snd_add]
  ring

private theorem spectral_exp_sum (t : ℝ) {ι : Type*} (S : Finset ι) (f : ι → ℝ × ℝ) :
    Circle.exp (2 * Real.pi * spectralPairing t (∑ i ∈ S, f i)) =
      ∏ i ∈ S, Circle.exp (2 * Real.pi * spectralPairing t (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [spectralPairing]
  | @insert i S hi ih => simp [hi, spectral_exp_add, ih]

/-- Finite-place character defined by the weighted logarithm, with the paper's positive `2π` sign.
Its inverse is taken only when forming a Fourier integrand. -/
def character (t : ℝ) : PontryaginDual Points where
  toFun x := Circle.exp (2 * Real.pi * spectralPairing t (logarithm x))
  map_one' := by simp [spectralPairing]
  map_mul' x y := by rw [logarithm_mul, spectral_exp_add]
  continuous_toFun := by
    have h : Continuous (fun n : ℝ × ℝ => 2 * Real.pi * spectralPairing t n) := by
      unfold spectralPairing
      fun_prop
    exact Circle.exp.continuous.comp (h.comp continuous_logarithm)

theorem character_apply (t : ℝ) (x : Points) :
    character t x = Circle.exp (2 * Real.pi * spectralPairing t (logarithm x)) := rfl

@[simp]
theorem character_zero : character 0 = 1 := by
  apply DFunLike.ext
  intro x
  change Circle.exp (2 * Real.pi * spectralPairing 0 (logarithm x)) = 1
  simp [spectralPairing]

theorem character_multipliable (t : ℝ) (x : Points) :
    Multipliable (fun p => (family p).character t (x p)) :=
  RestrictedProductFunctions.multipliable _ (fun p => local_character_one p t) x

/-- The exponential of the finite adelic logarithm is the product of the original local characters. -/
theorem character_eq_tprod (t : ℝ) (x : Points) :
    character t x = ∏' p : Nat.Primes, (family p).character t (x p) := by
  classical
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.eventually
  have hS : ∀ p ∉ hfin.toFinset, x p ∈ (family p).maxCompact := by
    intro p hp
    simpa using hp
  rw [character_apply, logarithm_eq_sum x hfin.toFinset hS, spectral_exp_sum,
    RestrictedProductFunctions.prod_eq_prod _ (fun p => local_character_one p t) x hfin.toFinset hS]
  exact Finset.prod_congr rfl fun p _ => (local_character_formula p t (x p)).symm

/-- Include one original local point, using the identity at every other prime. -/
def includeLocal (p : Nat.Primes) (x : (family p).Carrier) : Points :=
  RestrictedProduct.mulSingle (fun p => (family p).maxCompact) p x

@[simp]
theorem includeLocal_same (p : Nat.Primes) (x : (family p).Carrier) :
    includeLocal p x p = x := by simp [includeLocal]

theorem includeLocal_ne (p q : Nat.Primes) (x : (family p).Carrier) (h : q ≠ p) :
    includeLocal p x q = 1 := by
  simp [includeLocal, Pi.mulSingle_eq_of_ne h]

theorem continuous_includeLocal (p : Nat.Primes) : Continuous (includeLocal p) :=
  RestrictedProductFunctions.continuous_mulSingle (fun p => (family p).maxCompact) p

/-- The finite adelic height recovers the original local factor at every prime. -/
theorem inverseHeight_includeLocal (p : Nat.Primes) (s₀ σ : ℂ) (x : (family p).Carrier) :
    inverseHeight s₀ σ (includeLocal p x) = (family p).inverseHeight s₀ σ x := by
  unfold inverseHeight
  rw [tprod_eq_mulSingle p]
  · rw [includeLocal_same]
  · intro q hq
    rw [includeLocal_ne p q x hq]
    exact local_height_one q s₀ σ 1 (family q).maxCompact.one_mem

theorem logarithm_includeLocal (p : Nat.Primes) (x : (family p).Carrier) :
    logarithm (includeLocal p x) = localLogarithm p x := by
  unfold logarithm
  rw [tsum_eq_single p]
  · rw [includeLocal_same]
  · intro q hq
    rw [includeLocal_ne p q x hq]
    exact local_logarithm_zero q 1 (family q).maxCompact.one_mem

/-- Every local component of this finite adelic character is the one used in the proved integrals. -/
theorem character_includeLocal (p : Nat.Primes) (t : ℝ) (x : (family p).Carrier) :
    character t (includeLocal p x) = (family p).character t x := by
  rw [character_apply, logarithm_includeLocal, local_character_formula]

end Cubic.PoissonSummation.FiniteAdelicData
