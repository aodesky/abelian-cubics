import Cubic.PoissonSummation.FiniteEulerProductDomination
import Cubic.PoissonSummation.HaarNormalization
import Cubic.PoissonSummation.CountableQuotient
import CubicTargets.PoissonSummation.FiniteFourierProduct
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Analytic conclusions and conditional assembly of `lemma:finiteFourierProduct`

The explicit product's analytic clauses and the lattice-sum evaluations are proved.
The final conditional theorem uses `LocalValuationDescription D`: valuation exact
sequences, pointwise integrand formulas, and an index-six indicator description
at 3. Integrability and the integral-to-lattice formulas follow by pushing Haar
measure to counting measure; `1/6` follows from normalization. The original
local-data construction and its adelic comparison are proved in subsequent
modules. `AdelicFiniteFourierProduct` assembles the concrete paper proof;
this generic conditional theorem alone does not prove the paper lemma.
-/

noncomputable section

namespace Cubic.PoissonSummation

open MeasureTheory
open FiniteEulerProduct
open CubicTargets.PoissonSummation.FiniteFourierProduct

/-- All analytic clauses for the displayed Euler product, without a Fourier identification. -/
theorem finiteEulerProduct_analytic : AnalyticClaim where
  absolute_split := absolute_split
  absolute_inert := absolute_inert
  convergent_split := convergent_split
  convergent_inert := convergent_inert
  locally_uniform_split := locally_uniform_split
  locally_uniform_inert := locally_uniform_inert
  half_plane_bound := half_plane_bound

private abbrev PrimeCases := Unit ⊕ (InertPrimes ⊕ SplitPrimes)

private def primeOfCase : PrimeCases → Nat.Primes :=
  Sum.elim (fun _ => primeThree) (Sum.elim Subtype.val Subtype.val)

private theorem primeOfCase_injective : Function.Injective primeOfCase := by
  rintro (u | (q | p)) (v | (r | s)) h
  · cases u; cases v; rfl
  · have hr := r.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hr] at he
  · have hs := s.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hs] at he
  · have hq := q.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hq] at he
  · exact congrArg (fun a => Sum.inr (Sum.inl a)) (Subtype.ext h)
  · have hq := q.property
    have hs := s.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, hq, hs] at he
  · have hp := p.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hp] at he
  · have hp := p.property
    have hr := r.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, hp, hr] at he
  · exact congrArg (fun a => Sum.inr (Sum.inr a)) (Subtype.ext h)

private theorem primeOfCase_surjective : Function.Surjective primeOfCase := by
  intro p
  by_cases h3 : p = primeThree
  · exact ⟨Sum.inl (), h3.symm⟩
  have h0 : (p : ℕ) % 3 ≠ 0 := by
    intro h
    have he : (p : ℕ) = 3 := (p.prop.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h)
    exact h3 (Subtype.ext he)
  by_cases h2 : (p : ℕ) % 3 = 2
  · exact ⟨Sum.inr (Sum.inl ⟨p, h2⟩), rfl⟩
  · have h1 : (p : ℕ) % 3 = 1 := by omega
    exact ⟨Sum.inr (Sum.inr ⟨p, h1⟩), rfl⟩

private def primeCasesEquiv : PrimeCases ≃ Nat.Primes :=
  Equiv.ofBijective primeOfCase ⟨primeOfCase_injective, primeOfCase_surjective⟩

/-- Assemble the exceptional prime and the two residue classes, with convergence
proved on each class. This also serves the later extraction of the zeta factor. -/
theorem hasProd_primes_mod_three {f : Nat.Primes → ℂ} {a b : ℂ}
    (hi : HasProd (fun p : InertPrimes => f p.1) a)
    (hs : HasProd (fun p : SplitPrimes => f p.1) b) :
    HasProd f (f primeThree * a * b) := by
  have h3 : HasProd (fun _ : Unit => f primeThree) (f primeThree) := by simp
  have hrest : HasProd (fun c : InertPrimes ⊕ SplitPrimes =>
      f (Sum.elim Subtype.val Subtype.val c)) (a * b) := HasProd.sum hi hs
  have hall : HasProd (fun c : PrimeCases => f (primeOfCase c))
      (f primeThree * (a * b)) := HasProd.sum h3 hrest
  simpa only [mul_assoc] using (primeCasesEquiv.hasProd_iff (f := f)).mp hall

/-- Conditional evaluation of the product of actual integrals. The three local
calculations are hypotheses, and the exceptional prime occurs exactly once. -/
theorem finiteFourier_hasProd_of_localCalculation {D : LocalFamily} (hD : LocalCalculation D)
    (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    HasProd (fun p : Nat.Primes => localFourier (D p) s₀ σ t)
      (value (spectralParameter σ t)) := by
  let z := spectralParameter σ t
  have hz : 1 < z.re := by simpa [z] using hσ
  have hi : HasProd (fun p : InertPrimes => localFourier (D p.1) s₀ σ t)
      (∏' p : InertPrimes, inertFactor p z) := by
    convert (convergent_inert z hz).hasProd using 1
    funext p
    exact hD.inert p s₀ σ t hσ
  have hs : HasProd (fun p : SplitPrimes => localFourier (D p.1) s₀ σ t)
      (∏' p : SplitPrimes, splitFactor p z) := by
    convert (convergent_split z hz).hasProd using 1
    funext p
    exact hD.split p s₀ σ t hσ
  have h3 : HasProd (fun _ : Unit => localFourier (D primeThree) s₀ σ t) (1 / 6) := by
    simp [hD.at_three s₀ σ t hσ]
  have hrest : HasProd
      (fun c : InertPrimes ⊕ SplitPrimes =>
        localFourier (D (Sum.elim Subtype.val Subtype.val c)) s₀ σ t)
      ((∏' p : InertPrimes, inertFactor p z) * (∏' p : SplitPrimes, splitFactor p z)) :=
    HasProd.sum (f := fun c : InertPrimes ⊕ SplitPrimes =>
      localFourier (D (Sum.elim Subtype.val Subtype.val c)) s₀ σ t) hi hs
  have hall : HasProd (fun c : PrimeCases => localFourier (D (primeOfCase c)) s₀ σ t)
      ((1 / 6) * ((∏' p : InertPrimes, inertFactor p z) *
        (∏' p : SplitPrimes, splitFactor p z))) :=
    HasProd.sum (f := fun c : PrimeCases => localFourier (D (primeOfCase c)) s₀ σ t) h3 hrest
  have h := (primeCasesEquiv.hasProd_iff
    (f := fun p : Nat.Primes => localFourier (D p) s₀ σ t)).mp hall
  simpa only [value, mul_assoc] using h

/-- Conditional assembly of every clause of `lemma:finiteFourierProduct`.

This does not prove the paper lemma: its canonical `LocalFamily` and the proof of
`LocalCalculation` for that family remain necessary. In particular, the factor at 3
comes from the `at_three` integral hypothesis, not from a redefinition of the LHS.
-/
theorem finiteFourierProduct_of_localCalculation {D : LocalFamily}
    (hD : LocalCalculation D) : Claim D := by
  have heq : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
      finiteFourier D s₀ σ t = value (spectralParameter σ t) :=
    fun s₀ σ t hσ => (finiteFourier_hasProd_of_localCalculation hD s₀ σ t hσ).tprod_eq
  refine {
    local_integrable := hD.integrable
    finite_convergent := fun s₀ σ t hσ =>
      (finiteFourier_hasProd_of_localCalculation hD s₀ σ t hσ).multipliable
    spectral_product := heq
    trivial_value_real := ?_
    domination := ?_
    analytic := finiteEulerProduct_analytic }
  · intro s₀ σ hσ
    rw [heq s₀.re σ 0 hσ, spectralParameter_zero]
    have h := Complex.nonneg_iff.mp (value_nonneg σ hσ)
    exact ⟨h.2.symm, h.1⟩
  · intro s₀ σ t hσ
    rw [heq s₀ σ t hσ, heq s₀.re σ.re 0 hσ, spectralParameter_zero]
    simpa only [spectralParameter_re] using
      norm_value_le_real (spectralParameter σ t) (by simpa using hσ)

/-- Haar normalization yields `1/6` once the local integrand is the unit indicator
of an index-six subgroup of the maximal compact. The arithmetic index and the
actual height/character support identification are still explicit hypotheses. -/
theorem localFourier_eq_one_sixth_of_indicator (D : LocalData) (H : Subgroup D.maxCompact)
    (hH : MeasurableSet (H : Set D.maxCompact)) (hindex : H.index = 6)
    (s₀ σ : ℂ) (t : ℝ)
    (hf : localIntegrand D s₀ σ t =
      (Subtype.val '' (H : Set D.maxCompact)).indicator (fun _ => (1 : ℂ))) :
    localFourier D s₀ σ t = 1 / 6 := by
  letI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by rw [hindex]; decide)
  have hK : MeasurableSet (D.maxCompact : Set D.Carrier) := D.open_compact.measurableSet
  have hm := subgroup_index_mul_measure D.measure D.maxCompact hK H hH
  have hmass : D.measure.real (Subtype.val '' (H : Set D.maxCompact)) = 1 / 6 := by
    rw [hindex] at hm
    have hnorm : D.measure.real (D.maxCompact : Set D.Carrier) = 1 := by
      simp [Measure.real, D.normalized]
    rw [hnorm] at hm
    norm_num at hm
    linarith
  change (∫ x, localIntegrand D s₀ σ t x ∂D.measure) = 1 / 6
  rw [hf]
  have hi := integral_indicator_const (μ := D.measure) (1 : ℂ)
    ((MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr hH)
  calc
    _ = D.measure.real (Subtype.val '' (H : Set D.maxCompact)) • (1 : ℂ) := hi
    _ = 1 / 6 := by rw [hmass]; norm_num

/-- Evaluate the lattice sums and the exceptional indicator integral. -/
theorem localCalculation_of_latticeExpansion {D : LocalFamily}
    (hD : LocalLatticeExpansion D) : LocalCalculation D := by
  refine {
    integrable := hD.integrable
    split := ?_
    inert := ?_
    at_three := ?_ }
  · intro p s₀ σ t hσ
    rw [hD.split p s₀ σ t hσ]
    exact (LatticeSeries.hasSum_split p (spectralParameter σ t) (by simpa using hσ)).tsum_eq
  · intro p s₀ σ t hσ
    rw [hD.inert p s₀ σ t hσ]
    exact (LatticeSeries.hasSum_inert p (spectralParameter σ t) (by simpa using hσ)).tsum_eq
  · intro s₀ σ t hσ
    obtain ⟨H, hH, hindex, hf⟩ := hD.at_three
    exact localFourier_eq_one_sixth_of_indicator (D primeThree) H hH hindex s₀ σ t
      (hf s₀ σ t hσ)

/-- The full conclusion, conditional only on the canonical local-data construction
and the specified integral-to-lattice and exceptional-support identifications. -/
theorem finiteFourierProduct_of_latticeExpansion {D : LocalFamily}
    (hD : LocalLatticeExpansion D) : Claim D :=
  finiteFourierProduct_of_localCalculation (localCalculation_of_latticeExpansion hD)

/-- A measurable subgroup of the normalized compact has integrable unit indicator.
No separate integrability hypothesis is needed at the exceptional prime. -/
theorem localIntegrand_integrable_of_indicator (D : LocalData) (H : Subgroup D.maxCompact)
    (hH : MeasurableSet (H : Set D.maxCompact)) (s₀ σ : ℂ) (t : ℝ)
    (hf : localIntegrand D s₀ σ t =
      (Subtype.val '' (H : Set D.maxCompact)).indicator (fun _ => (1 : ℂ))) :
    Integrable (localIntegrand D s₀ σ t) D.measure := by
  have hK : MeasurableSet (D.maxCompact : Set D.Carrier) := D.open_compact.measurableSet
  have hmeas := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr hH
  have hsub : Subtype.val '' (H : Set D.maxCompact) ⊆ (D.maxCompact : Set D.Carrier) := by
    rintro x ⟨k, _, rfl⟩
    exact k.2
  have hfinite : D.measure (Subtype.val '' (H : Set D.maxCompact)) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono hsub).trans_lt (by rw [D.normalized]; exact ENNReal.one_lt_top)
  rw [hf]
  exact (integrable_indicator_iff hmeas).mpr (integrableOn_const hfinite)

/-- Derive a local Fourier series and its integrability from a valuation exact
sequence and the pointwise integrand. The countable-quotient theorem supplies
the integration step; the lattice weights supply absolute convergence. -/
theorem localFourier_of_valuation {Γ I : Type} [Group Γ] [Countable Γ]
    (D : LocalData) (V : LocalValuation D Γ) (e : I ↪ Γ)
    (w : I → ℂ) (hw : Summable w) (s₀ σ : ℂ) (t : ℝ)
    (hf : localIntegrand D s₀ σ t = (Function.extend e w 0) ∘ V.valuation) :
    Integrable (localIntegrand D s₀ σ t) D.measure ∧
      localFourier D s₀ σ t = ∑' n, w n := by
  letI : MeasurableSpace Γ := ⊤
  have hm : Measurable V.valuation := measurable_of_countable_ker V.valuation
    (by rw [V.kernel]; exact D.open_compact.measurableSet)
  have hv := measurePreserving_count_of_ker D.measure V.valuation hm V.surjective
    (by rw [V.kernel]; exact D.normalized)
  change Integrable (localIntegrand D s₀ σ t) D.measure ∧
    (∫ x, localIntegrand D s₀ σ t x ∂D.measure) = ∑' n, w n
  rw [hf]
  exact integrable_and_integral_eq_tsum_of_extend hv e hw

/-- The geometric valuation and integrand descriptions imply both local
integrability and the actual integral-to-lattice identities. -/
theorem localLatticeExpansion_of_valuationDescription {D : LocalFamily}
    (hD : LocalValuationDescription D) : LocalLatticeExpansion D := by
  letI : Countable (Multiplicative (ℤ × ℤ)) := Multiplicative.toAdd.injective.countable
  letI : Countable (Multiplicative OrbitParametrization.CocharacterLattice.invariantLattice) :=
    Multiplicative.toAdd.injective.countable
  have hs : ∀ (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
      Integrable (localIntegrand (D p.1) s₀ σ t) (D p.1).measure ∧
      localFourier (D p.1) s₀ σ t =
        ∑' n, LatticeSeries.weight p.1 (spectralParameter σ t) n := by
    intro p s₀ σ t hσ
    obtain ⟨V, hf⟩ := hD.split p
    exact localFourier_of_valuation (D p.1) V LatticeCone.splitEmbedding _
      (LatticeSeries.hasSum_split p (spectralParameter σ t) (by simpa using hσ)).summable
      s₀ σ t (hf s₀ σ t hσ)
  have hi : ∀ (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
      Integrable (localIntegrand (D p.1) s₀ σ t) (D p.1).measure ∧
      localFourier (D p.1) s₀ σ t =
        ∑' n : LatticeCone.InvariantConePoint,
          LatticeSeries.weight p.1 (spectralParameter σ t) n.1 := by
    intro p s₀ σ t hσ
    obtain ⟨V, hf⟩ := hD.inert p
    exact localFourier_of_valuation (D p.1) V LatticeCone.inertEmbedding _
      (LatticeSeries.hasSum_inert p (spectralParameter σ t) (by simpa using hσ)).summable
      s₀ σ t (hf s₀ σ t hσ)
  refine {
    integrable := ?_
    split := fun p s₀ σ t hσ => (hs p s₀ σ t hσ).2
    inert := fun p s₀ σ t hσ => (hi p s₀ σ t hσ).2
    at_three := hD.at_three }
  intro p s₀ σ t hσ
  obtain ⟨c, rfl⟩ := primeOfCase_surjective p
  rcases c with u | (q | p)
  · obtain ⟨H, hH, _, hf⟩ := hD.at_three
    exact localIntegrand_integrable_of_indicator (D primeThree) H hH s₀ σ t (hf s₀ σ t hσ)
  · exact (hi q s₀ σ t hσ).1
  · exact (hs p s₀ σ t hσ).1

/-- Every conclusion of Lemma 5 follows from the canonical local geometry.
Neither integrability nor integral evaluations are hypotheses of this theorem.
The original-point family and its geometric description are supplied separately. -/
theorem finiteFourierProduct_of_valuationDescription {D : LocalFamily}
    (hD : LocalValuationDescription D) : Claim D :=
  finiteFourierProduct_of_latticeExpansion (localLatticeExpansion_of_valuationDescription hD)

end Cubic.PoissonSummation
