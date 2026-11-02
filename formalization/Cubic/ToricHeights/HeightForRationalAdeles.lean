import CubicTargets.ToricHeights.HeightForRationalAdeles

/-!
# Proof of `eqn:heightforrationaladeles`

The paper's argument: `φ(ℓ_w(x_v))` is independent of `w | v` by Galois invariance of `φ`
(`supportFunction_swap`; the second split place has the swapped cocharacter,
`splitSecondCoordinates_eq`), and the `g` equal factors `(q_v^{f}... )^{1/[E:ℚ]}` over `v`
combine, using `e f g = [E:ℚ]`, to `q_v^{-φ(ℓ_w)/e_v}`
(`LocalDegreeNormalization.split_height_product`; for the inert prime `q_w = p²`, for the
ramified prime `q_w = 3`, and at infinity `q_w = e²`). The adelic height is then the product
of these grouped factors (`FiniteAdelicData.inverseHeight` is a `tprod` with finite
multiplicative support, `height_multipliable`).
-/

noncomputable section

namespace Cubic.ToricHeights.HeightForRationalAdeles

open Cubic.QuadraticCorrespondence Cubic.PoissonSummation QuotientFiniteHeight
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open CubicTargets.ToricHeights.HeightForRationalAdeles

private theorem transport_property
    (P : (D : LocalData) → (D.Carrier → ℝ × ℝ) → Prop)
    {D F : LocalData} (h : D = F) (f : F.Carrier → ℝ × ℝ) (hf : P F f) :
    P D ((congrArg (fun D => D.Carrier → ℝ × ℝ) h).mpr f) := by
  subst F
  exact hf

/-- Case analysis on the splitting type of `p`, transporting the cocharacter. -/
theorem placeCocharacter_induction (p : Nat.Primes)
    (P : (D : LocalData) → (D.Carrier → ℝ × ℝ) → Prop)
    (hsplit : ∀ (_ : Fact (p : ℕ).Prime) (h : (p : ℕ) % 3 = 1),
      haveI : Fact ((p : ℕ) % 3 = 1) := ⟨h⟩
      P (splitData ⟨p, h⟩) (splitCoordinates p))
    (hinert : ∀ (_ : Fact (p : ℕ).Prime) (h : (p : ℕ) % 3 = 2),
      haveI : Fact ((p : ℕ) % 3 = 2) := ⟨h⟩
      P (inertData ⟨p, h⟩) (inertCoordinates p))
    (hthree : (p : ℕ) = 3 → P ramifiedData ramifiedCoordinates) :
    P (family p) (placeCocharacter p) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · simp only [placeCocharacter, dif_pos hs]
    exact transport_property P (family_split ⟨p, hs⟩) _ (hsplit ⟨p.2⟩ hs)
  by_cases hi : (p : ℕ) % 3 = 2
  · simp only [placeCocharacter, dif_neg hs, dif_pos hi]
    exact transport_property P (family_inert ⟨p, hi⟩) _ (hinert ⟨p.2⟩ hi)
  · simp only [placeCocharacter, dif_neg hs, dif_neg hi]
    have h3 : (p : ℕ) = 3 := by
      have h0 : (p : ℕ) % 3 = 0 := by omega
      exact (p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)
    exact transport_property P (by simp [family, hs, hi]) _ (hthree h3)

private theorem cast_two_div (z : ℂ) : z / ((2 : ℕ) : ℂ) = z / 2 := by norm_num

/-- The grouped local factor at every prime. -/
theorem local_factor (s₀ σ : ℂ) (p : Nat.Primes) (y : (family p).Carrier) :
    (family p).inverseHeight (-s₀) (-σ) y = localFactor s₀ σ p y := by
  unfold localFactor
  revert y
  apply placeCocharacter_induction p
    (fun D L => ∀ y, D.inverseHeight (-s₀) (-σ) y =
      (p : ℂ) ^ (-supportFunction s₀ σ (L y) / (ramificationIndex p : ℂ)))
  · intro _ hs y
    haveI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    have he : ramificationIndex p = 1 := by simp [ramificationIndex]; omega
    change splitInverseHeight p (-s₀) (-σ) y = _
    rw [splitInverseHeight, LocalLogarithmNormalization.padic_residue_cardinality,
      CyclotomicField.finrank_eq_two, splitSecondCoordinates_eq, supportFunction_neg,
      supportFunction_neg, cast_two_div, cast_two_div, he, Nat.cast_one,
      div_one]
    exact LocalDegreeNormalization.split_height_product p s₀ σ _
  · intro _ hi y
    haveI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    have he : ramificationIndex p = 1 := by simp [ramificationIndex]; omega
    change inertInverseHeight p (-s₀) (-σ) y = _
    rw [inertInverseHeight, CyclotomicInertField.card_residueField, CyclotomicField.finrank_eq_two,
      Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, supportFunction_neg, he, Nat.cast_one,
      div_one]
    congr 1
    push_cast
    ring
  · intro h3 y
    have he : ramificationIndex p = 2 := by simp [ramificationIndex, h3]
    have hp : (p : ℂ) = ((3 : ℕ) : ℂ) := by rw [h3]
    change ramifiedInverseHeight (-s₀) (-σ) y = _
    rw [ramifiedInverseHeight, CyclotomicRamifiedField.card_residueField,
      CyclotomicField.finrank_eq_two, supportFunction_neg, he, hp, neg_div]

/-- The archimedean factor: `(e²)^{φ_{-s}(ℓ)/[E:ℚ]} = e^{-φ(ℓ)}`. -/
theorem archimedean_factor (s₀ σ : ℂ) (P : ArchimedeanQuotientLogarithm.Points) :
    ArchimedeanQuotientLogarithm.inverseHeight (-s₀) (-σ) P =
      (Real.exp 1 : ℂ) ^ (-supportFunction s₀ σ (ArchimedeanQuotientLogarithm.localCocharacter P)) := by
  rw [ArchimedeanQuotientLogarithm.inverseHeight, CyclotomicField.finrank_eq_two,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero (2 : ℝ)),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero (1 : ℝ)),
    ← Complex.ofReal_log (Real.exp_pos 2).le, ← Complex.ofReal_log (Real.exp_pos 1).le,
    Real.log_exp, Real.log_exp, supportFunction_neg]
  congr 1
  push_cast
  ring

theorem «eqn:heightforrationaladeles» : Claim where
  independent p _ _ s₀ σ P := by
    rw [splitSecondCoordinates_eq, supportFunction_swap]
  multipliable s₀ σ x := by
    have h := FiniteAdelicData.height_multipliable (-s₀) (-σ) x.2
    simpa only [local_factor] using h
  height_eq s₀ σ x := by
    change ArchimedeanQuotientLogarithm.inverseHeight (-s₀) (-σ) x.1 *
      FiniteAdelicData.inverseHeight (-s₀) (-σ) x.2 = _
    rw [archimedean_factor, FiniteAdelicData.inverseHeight]
    simp only [local_factor]

end Cubic.ToricHeights.HeightForRationalAdeles
