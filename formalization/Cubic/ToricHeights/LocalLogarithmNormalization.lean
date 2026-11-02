import Cubic.ToricHeights.SplitLocalHeight
import Cubic.ToricHeights.InertLocalHeight
import Cubic.ToricHeights.RamifiedLocalValuation
import Cubic.ToricHeights.LocalDegreeNormalization
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedResidueField
import Cubic.QuadraticCorrespondence.CyclotomicInertResidueField

/-!
# Local logarithms, norm signs and the spectral pairing

The local height coordinates are `ell_w/e_v`. Multiplying by `log p` gives
a representative logarithmic vector. At a split prime the adelic logarithm
averages this vector with its conjugate; invariant spectral functionals have
the same value on both. The
invariant spectral functional has values `t,-t/2,-t/2` on `v₀,v₁,v₂`.
We check that its `exp(2π i ·)` character is exactly each constructed local
character, and relate the total coordinate to the local norms.

These are finite-place comparisons for the local models; the adelic logarithm
is assembled in `Cubic.PoissonSummation.FiniteAdelicData`.
-/

noncomputable section

namespace Cubic.ToricHeights.LocalLogarithmNormalization

open Cubic.OrbitParametrization
open Cubic.QuadraticCorrespondence

/-- The logarithmic coordinate from an already ramification-normalized valuation vector. -/
def normalizedLog (q : ℝ) (n : ℝ × ℝ) : ℝ × ℝ :=
  (Real.log q * n.1, Real.log q * n.2)

/-- One splitting-field place's contribution, weighted by the global degree `D`.
Here `q_w` is its residue cardinality; `n` has not been divided by `e_v`. -/
def placeContribution (D : ℕ) (q_w : ℝ) (n : ℝ × ℝ) : ℝ × ℝ :=
  (Real.log q_w * n.1 / D, Real.log q_w * n.2 / D)

/-- The invariant spectral functional specified by its value on `v₀`. -/
def spectralPairing (t : ℝ) (n : ℝ × ℝ) : ℝ := -t / 2 * (n.1 + n.2)

/-- Average over the two Galois conjugates in ray coordinates. -/
def conjugateAverage (n : ℝ × ℝ) : ℝ × ℝ :=
  ((n.1 + n.2) / 2, (n.2 + n.1) / 2)

theorem spectralPairing_conjugateAverage (t : ℝ) (n : ℝ × ℝ) :
    spectralPairing t (conjugateAverage n) = spectralPairing t n := by
  simp only [spectralPairing, conjugateAverage]
  ring

/-- The split-place contribution is the sum over two places divided by `[E:ℚ]=2`. -/
theorem conjugateAverage_normalizedLog (q : ℝ) (n : ℝ × ℝ) :
    conjugateAverage (normalizedLog q n) =
      ((Real.log q * n.1 + Real.log q * n.swap.1) / 2,
       (Real.log q * n.2 + Real.log q * n.swap.2) / 2) := rfl

theorem split_placeContributions (q : ℝ) (n : ℝ × ℝ) :
    placeContribution 2 q n + placeContribution 2 q n.swap =
      conjugateAverage (normalizedLog q n) := by
  ext <;> simp [placeContribution, conjugateAverage, normalizedLog] <;> ring

/-- Mathlib's residue-field equivalence supplies the cardinality of each split factor. -/
theorem padic_residue_cardinality (p : ℕ) [Fact p.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- The two split residue fields each contribute `log(p)/2`, before conjugate averaging. -/
theorem split_residue_placeContributions (p : ℕ) [Fact p.Prime] (n : ℝ × ℝ) :
    placeContribution 2 (Nat.card (IsLocalRing.ResidueField ℤ_[p])) n +
        placeContribution 2 (Nat.card (IsLocalRing.ResidueField ℤ_[p])) n.swap =
      conjugateAverage (normalizedLog p n) := by
  rw [padic_residue_cardinality]
  exact split_placeContributions p n

/-- Unlike the invariant spectral pairing, a support function cannot in general
be evaluated after averaging: conjugate vectors can lie in different cones. -/
theorem supportFunction_before_averaging (s₀ σ : ℂ) :
    supportFunction s₀ σ (1, -1) = -s₀ - 2 * σ ∧
      supportFunction s₀ σ (conjugateAverage (1, -1)) = 0 := by
  norm_num [supportFunction, conjugateAverage]
  ring

theorem spectralPairing_v0 (t : ℝ) : spectralPairing t (-1, -1) = t := by
  unfold spectralPairing
  ring

theorem spectralPairing_v1 (t : ℝ) : spectralPairing t (1, 0) = -t / 2 := by
  simp [spectralPairing]

theorem spectralPairing_v2 (t : ℝ) : spectralPairing t (0, 1) = -t / 2 := by
  simp [spectralPairing]

/-- The factor `2π` and the spectral value `-t/2` account for the sign and factor `π`. -/
theorem phase_eq (q t d : ℝ) (n : ℝ × ℝ) (hd : n.1 + n.2 = d) :
    2 * Real.pi * spectralPairing t (normalizedLog q n) = -Real.pi * t * Real.log q * d := by
  unfold spectralPairing normalizedLog
  dsimp
  rw [← mul_add, hd]
  ring

theorem log_norm_padic (p : ℕ) [Fact p.Prime] (x : ℚ_[p]ˣ) :
    Real.log ‖(x : ℚ_[p])‖ = -(Padic.valuation (x : ℚ_[p]) : ℝ) * Real.log p := by
  rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero, Real.log_zpow]
  push_cast
  rfl

theorem split_degree (p : ℕ) [Fact p.Prime] (x : SplitLocalModel.Points p) :
    SplitLocalModel.degree p x = Padic.valuation (x.1 : ℚ_[p]) + Padic.valuation (x.2 : ℚ_[p]) := by
  simp only [SplitLocalModel.degree, SplitLocalModel.valuation, PadicMultiplicative.valuation,
    CocharacterIsomorphism.fromCyclotomic, MonoidHom.coe_mk, OneHom.coe_mk,
    AddEquiv.coe_mk, Equiv.coe_fn_mk]
  dsimp
  ring

/-- At a split place the norm is the product of the two p-adic absolute values. -/
theorem split_log_norm (p : ℕ) [Fact p.Prime] (x : SplitLocalModel.Points p) :
    Real.log p * (SplitLocalModel.degree p x : ℝ) =
      -Real.log (‖(x.1 : ℚ_[p])‖ * ‖(x.2 : ℚ_[p])‖) := by
  rw [Real.log_mul (norm_ne_zero_iff.mpr x.1.ne_zero) (norm_ne_zero_iff.mpr x.2.ne_zero),
    log_norm_padic, log_norm_padic, split_degree]
  push_cast
  ring

theorem split_character (p : ℕ) [Fact p.Prime] (t : ℝ) (x : SplitLocalModel.Points p) :
    SplitLocalModel.character p t x =
      Circle.exp (2 * Real.pi * spectralPairing t (normalizedLog p (SplitLocalModel.rayCoordinates p x))) := by
  rw [phase_eq p t _ _ (SplitLocalModel.rayCoordinates_sum p x)]
  rfl

/-- The same character is obtained from the two-place average. -/
theorem split_character_averaged (p : ℕ) [Fact p.Prime] (t : ℝ)
    (x : SplitLocalModel.Points p) :
    SplitLocalModel.character p t x = Circle.exp (2 * Real.pi * spectralPairing t
      (conjugateAverage (normalizedLog p (SplitLocalModel.rayCoordinates p x)))) := by
  rw [spectralPairing_conjugateAverage]
  exact split_character p t x

/-- The split logarithm is invariant and has the minus sign of the local norm formula. -/
theorem split_averaged_log_norm (p : ℕ) [Fact p.Prime] (x : SplitLocalModel.Points p) :
    conjugateAverage (normalizedLog p (SplitLocalModel.rayCoordinates p x)) =
      (-Real.log (‖(x.1 : ℚ_[p])‖ * ‖(x.2 : ℚ_[p])‖) / 2,
       -Real.log (‖(x.1 : ℚ_[p])‖ * ‖(x.2 : ℚ_[p])‖) / 2) := by
  have h := split_log_norm p x
  rw [← SplitLocalModel.rayCoordinates_sum] at h
  ext <;> simp only [conjugateAverage, normalizedLog] <;> nlinarith

/-- At an inert place both character coordinates have valuation `ord`, so the norm degree is two. -/
theorem inert_log_norm (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : InertLocalModel.Points p) :
    Real.log p * (InertLocalModel.degree p x : ℝ) =
      -2 * Real.log ‖(x : CyclotomicInertField.Extension p)‖ := by
  rw [InertLocalModel.norm_eq_zpow_ord, Real.log_zpow, InertLocalModel.degree_eq_two_ord]
  push_cast
  ring

theorem inert_character (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (t : ℝ) (x : InertLocalModel.Points p) :
    InertLocalModel.character p t x =
      Circle.exp (2 * Real.pi * spectralPairing t (normalizedLog p (InertLocalModel.rayCoordinates p x))) := by
  rw [phase_eq p t _ _ (InertLocalModel.rayCoordinates_sum p x)]
  rfl

/-- The inert extension has both ray coordinates equal to its integral valuation. -/
theorem inert_rayCoordinates (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : InertLocalModel.Points p) :
    InertLocalModel.rayCoordinates p x = ((InertLocalModel.ord p x : ℝ), (InertLocalModel.ord p x : ℝ)) := by
  simp [InertLocalModel.rayCoordinates, InertLocalModel.valuation_coordinates]

/-- For the inert-place weight, `q_w=p²` cancels the global degree two;
there is no extra `1/2` in the final logarithmic vector. -/
theorem inert_weightedLog (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : InertLocalModel.Points p) :
    placeContribution 2 ((p : ℝ) ^ 2) ((InertLocalModel.ord p x : ℝ), (InertLocalModel.ord p x : ℝ)) =
        normalizedLog p (InertLocalModel.rayCoordinates p x) := by
  rw [inert_rayCoordinates]
  ext <;> simp [placeContribution, normalizedLog, Real.log_pow] <;> ring

/-- The local residue field has `p²` elements, so the normalized local absolute value
is the square of the extended p-adic norm. -/
theorem inert_residue_norm (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : InertLocalModel.Points p) :
    (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)) : ℝ) ^
        (-InertLocalModel.ord p x) =
      ‖(x : CyclotomicInertField.Extension p)‖ ^ 2 := by
  rw [CyclotomicInertField.card_residueField, Nat.cast_pow]
  simp only [InertLocalModel.norm_eq_zpow_ord, pow_two, mul_zpow]

/-- The proved residue cardinality cancels the global degree two in the local logarithm. -/
theorem inert_residue_weightedLog (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (x : InertLocalModel.Points p) :
    placeContribution 2 (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)))
        ((InertLocalModel.ord p x : ℝ), (InertLocalModel.ord p x : ℝ)) =
      normalizedLog p (InertLocalModel.rayCoordinates p x) := by
  rw [CyclotomicInertField.card_residueField, Nat.cast_pow]
  exact inert_weightedLog p x

/-- At three the extended base-field norm already incorporates the factor `1/e₃ = 1/2`. -/
theorem ramified_log_norm (x : RamifiedLocalModel.Points) :
    Real.log 3 * RamifiedLocalModel.degree x =
      -2 * Real.log ‖(x : CyclotomicRamifiedField.Extension)‖ := by
  have hlog : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  unfold RamifiedLocalModel.degree RamifiedLocalModel.logarithmicOrder
  field_simp

theorem ramified_character (t : ℝ) (x : RamifiedLocalModel.Points) :
    RamifiedLocalModel.character t x =
      Circle.exp (2 * Real.pi * spectralPairing t (normalizedLog 3 (RamifiedLocalModel.rayCoordinates x))) := by
  have hs : (RamifiedLocalModel.rayCoordinates x).1 +
      (RamifiedLocalModel.rayCoordinates x).2 = RamifiedLocalModel.degree x := by
    unfold RamifiedLocalModel.rayCoordinates RamifiedLocalModel.degree
    dsimp
    ring
  rw [phase_eq 3 t _ _ hs]
  rfl

/-- The ramified parameter has total degree one, whereas the rational prime has degree two. -/
theorem ramified_parameter_degree : RamifiedLocalModel.degree RamifiedLocalModel.ramifiedParameter = 1 := by
  rw [RamifiedLocalModel.degree, RamifiedLocalModel.logarithmicOrder_ramifiedParameter]
  norm_num

theorem ramified_scalar_degree : RamifiedLocalModel.degree RamifiedLocalModel.scalarThree = 2 := by
  rw [RamifiedLocalModel.degree, RamifiedLocalModel.logarithmicOrder_scalarThree]
  norm_num

/-- On the whole ramified group, the ray coordinates are the integral valuation
divided by two. No second ramification factor should be applied to them. -/
theorem ramified_rayCoordinates (x : RamifiedLocalModel.Points) :
    RamifiedLocalModel.rayCoordinates x = LocalDegreeNormalization.normalizedValuation 2
      ((RamifiedLocalModel.ord x : ℝ), (RamifiedLocalModel.ord x : ℝ)) := by
  simp only [RamifiedLocalModel.rayCoordinates,
    RamifiedLocalModel.logarithmicOrder_eq_ord_div_two, LocalDegreeNormalization.normalizedValuation]
  norm_num [div_eq_mul_inv, mul_comm]

/-- At three, `q_w=3`: division by the global degree survives as `1/e₃=1/2`. -/
theorem ramified_weightedLog (x : RamifiedLocalModel.Points) :
    placeContribution 2 3 ((RamifiedLocalModel.ord x : ℝ), (RamifiedLocalModel.ord x : ℝ)) =
        normalizedLog 3 (RamifiedLocalModel.rayCoordinates x) := by
  rw [ramified_rayCoordinates]
  ext <;> simp only [placeContribution, LocalDegreeNormalization.normalizedValuation, normalizedLog] <;> ring

/-- The local absolute value `q_w^(-ord_w)` uses the residue cardinality.
It is the square of the extended base-field norm at this degree-two place. -/
theorem ramified_residue_norm (x : RamifiedLocalModel.Points) :
    (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers) : ℝ) ^
        (-RamifiedLocalModel.ord x) =
      ‖(x : CyclotomicRamifiedField.Extension)‖ ^ 2 := by
  rw [CyclotomicRamifiedField.card_residueField]
  exact (RamifiedLocalModel.norm_sq_eq_zpow_ord x).symm

/-- Replace the numerical residue size by the cardinality of the local residue field. -/
theorem ramified_residue_weightedLog (x : RamifiedLocalModel.Points) :
    placeContribution 2 (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers))
        ((RamifiedLocalModel.ord x : ℝ), (RamifiedLocalModel.ord x : ℝ)) =
      normalizedLog 3 (RamifiedLocalModel.rayCoordinates x) := by
  rw [CyclotomicRamifiedField.card_residueField]
  exact ramified_weightedLog x

/-- At the complex place `q_w=exp 2`, the logarithmic weight is one after
division by `[E:ℚ]=2`. The archimedean `e_v` in the paper is one. -/
theorem complex_place_log_weight : Real.log (Real.exp 2) / 2 = 1 := by
  rw [Real.log_exp]
  norm_num

/-- The height uses `φ(ell_w)/e₃`, for every point and on all cones. -/
theorem ramified_inverseHeight_exponent (s₀ σ : ℂ) (x : RamifiedLocalModel.Points) :
    RamifiedLocalModel.inverseHeight s₀ σ x = (3 : ℂ) ^
      (supportFunction s₀ σ ((RamifiedLocalModel.ord x : ℝ), (RamifiedLocalModel.ord x : ℝ)) / 2) := by
  rw [RamifiedLocalModel.inverseHeight, ramified_rayCoordinates,
    LocalDegreeNormalization.supportFunction_normalizedValuation]
  norm_num

/-- An explicit height check on the ramified parameter, before the integrality cutoff. -/
theorem ramified_parameter_height (s₀ σ : ℂ) :
    RamifiedLocalModel.inverseHeight s₀ σ RamifiedLocalModel.ramifiedParameter = (3 : ℂ) ^ (-σ) := by
  unfold RamifiedLocalModel.inverseHeight RamifiedLocalModel.rayCoordinates
  rw [RamifiedLocalModel.logarithmicOrder_ramifiedParameter]
  congr 1
  norm_num [supportFunction]

end Cubic.ToricHeights.LocalLogarithmNormalization
