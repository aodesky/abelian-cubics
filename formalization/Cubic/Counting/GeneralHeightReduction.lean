import Cubic.Counting.CyclicPolynomialRealRoots
import CubicTargets.Counting.GeneralMonic
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Proof of `lemma:generalHeightReduction`

Following the paper: the roots `r₁, r₂, r₃` of `f ∈ F_mon` are real, since the Galois group
is `C₃`, so `n = ½ Σ (rᵢ - rⱼ)² ≥ 0`, with equality only for a triple rational root, which
is impossible. If `|a₂| ≤ H` and `|a₁| ≤ H²`, then `Σ rᵢ² = a₂² - 2a₁ ≤ 3H²`, and the
arithmetic–geometric mean inequality gives `|a₀| ≤ H³`. The substitutions `x ↦ εx - m` on
roots preserve `n` and the Galois group; they give the two bijections.
-/

noncomputable section

namespace Cubic.Counting.GeneralHeightReduction

open Polynomial Cubic.Counting.GeneralMonicData Cubic.Counting.PolynomialCountData
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open CubicTargets.Counting.GeneralMonic (signTranslate)

/-! ### The Galois group is unchanged by the substitutions -/

/-- Two polynomials with surjections between their Galois groups in both directions have
isomorphic Galois groups. -/
theorem cyclic_iff_of_surjective {p q : ℚ[X]}
    (h₁ : ∃ φ : p.Gal →* q.Gal, Function.Surjective φ)
    (h₂ : ∃ ψ : q.Gal →* p.Gal, Function.Surjective ψ) :
    HasCyclicCubicGaloisGroup p ↔ HasCyclicCubicGaloisGroup q := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  have hφb : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (Nat.card_le_card_of_surjective ψ hψ)
  exact ⟨fun ⟨e⟩ => ⟨(MulEquiv.ofBijective φ hφb).symm.trans e⟩,
    fun ⟨e⟩ => ⟨(MulEquiv.ofBijective φ hφb).trans e⟩⟩

/-- Composition with a degree-one polynomial having a degree-one inverse. -/
theorem cyclic_comp_iff {p q q' : ℚ[X]} (hq : q.natDegree = 1) (hq' : q'.natDegree = 1)
    (hqq : q.comp q' = X) :
    HasCyclicCubicGaloisGroup (p.comp q) ↔ HasCyclicCubicGaloisGroup p := by
  have hp : (p.comp q).comp q' = p := by rw [comp_assoc, hqq, comp_X]
  refine cyclic_iff_of_surjective ⟨Gal.restrictComp p q (by omega),
    Gal.restrictComp_surjective p q (by omega)⟩ ?_
  have h : ∃ ψ : ((p.comp q).comp q').Gal →* (p.comp q).Gal, Function.Surjective ψ :=
    ⟨Gal.restrictComp (p.comp q) q' (by omega), Gal.restrictComp_surjective _ _ (by omega)⟩
  rwa [hp] at h

/-- Multiplication by a nonzero constant. -/
theorem cyclic_C_mul_iff {p : ℚ[X]} {u : ℚ} (hu : u ≠ 0) (hp : p ≠ 0) :
    HasCyclicCubicGaloisGroup (C u * p) ↔ HasCyclicCubicGaloisGroup p := by
  have hup : C u * p ≠ 0 := mul_ne_zero (by simpa using hu) hp
  have hd : C u * p ∣ p := ⟨C u⁻¹, by rw [mul_comm, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu,
    C_1, one_mul]⟩
  exact cyclic_iff_of_surjective
    ⟨Gal.restrictDvd (dvd_mul_left p (C u)), Gal.restrictDvd_surjective _ hup⟩
    ⟨Gal.restrictDvd hd, Gal.restrictDvd_surjective hd hp⟩

theorem sign_cases {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

theorem signTranslate_map (ε m : ℤ) (f : ℤ[X]) :
    (signTranslate ε m f).map (Int.castRingHom ℚ) =
      C (ε : ℚ) * (f.map (Int.castRingHom ℚ)).comp (C (ε : ℚ) * (X + C (m : ℚ))) := by
  simp [signTranslate, Polynomial.map_mul, map_comp]

theorem cyclic_signTranslate_iff {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (m : ℤ) {f : ℤ[X]}
    (hf : f.map (Int.castRingHom ℚ) ≠ 0) :
    HasCyclicCubicGaloisGroup ((signTranslate ε m f).map (Int.castRingHom ℚ)) ↔
      HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ)) := by
  have hεq : (ε : ℚ) * ε = 1 := by exact_mod_cast sign_cases hε
  have hε0 : (ε : ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hεq
  have hdeg : ∀ k : ℚ, (C (ε : ℚ) * (X + C k)).natDegree = 1 := fun k => by
    rw [natDegree_C_mul hε0, natDegree_X_add_C]
  have hinv : (C (ε : ℚ) * (X + C (m : ℚ))).comp (C (ε : ℚ) * (X + C (-(ε * m : ℚ)))) = X := by
    have he : C (ε : ℚ) * C (ε : ℚ) = 1 := by rw [← C_mul, hεq, C_1]
    simp only [mul_comp, C_comp, add_comp, X_comp, map_neg, map_mul]
    linear_combination (X - C (ε : ℚ) * C (m : ℚ)) * he
  have hcomp : (f.map (Int.castRingHom ℚ)).comp (C (ε : ℚ) * (X + C (m : ℚ))) ≠ 0 := by
    intro h
    apply hf
    have := congrArg (fun p => p.comp (C (ε : ℚ) * (X + C (-(ε * m : ℚ))))) h
    simpa only [comp_assoc, hinv, comp_X, zero_comp] using this
  rw [signTranslate_map, cyclic_C_mul_iff hε0 hcomp, cyclic_comp_iff (hdeg _) (hdeg _) hinv]

/-! ### Coefficients -/

@[simp] theorem monicCubic_coeff_two (a₂ a₁ a₀ : ℤ) : (monicCubic a₂ a₁ a₀).coeff 2 = a₂ := by
  simp only [monicCubic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

@[simp] theorem monicCubic_coeff_one (a₂ a₁ a₀ : ℤ) : (monicCubic a₂ a₁ a₀).coeff 1 = a₁ := by
  simp only [monicCubic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

@[simp] theorem monicCubic_coeff_zero (a₂ a₁ a₀ : ℤ) : (monicCubic a₂ a₁ a₀).coeff 0 = a₀ := by
  simp only [monicCubic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

theorem monicCubic_map_ne_zero (a₂ a₁ a₀ : ℤ) :
    (monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ) ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff (Int.castRingHom ℚ).injective_int]
  intro h
  have := congrArg (fun p => p.coeff 3) h
  simp only [monicCubic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    coeff_zero] at this
  norm_num at this

theorem traceOneCubic_eq (a b : ℤ) : traceOneCubic a b = monicCubic (-1) a b := by
  simp [traceOneCubic, monicCubic, sub_eq_add_neg]

/-- The substitution on coefficients, for `ε = ±1`. -/
theorem signTranslate_monicCubic {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (m a₂ a₁ a₀ : ℤ) :
    signTranslate ε m (monicCubic a₂ a₁ a₀) =
      monicCubic (3 * m + ε * a₂) (3 * m ^ 2 + 2 * ε * a₂ * m + a₁)
        (m ^ 3 + ε * a₂ * m ^ 2 + a₁ * m + ε * a₀) := by
  rcases hε with rfl | rfl <;>
    simp only [signTranslate, monicCubic, add_comp, mul_comp, C_comp, X_comp, X_pow_comp,
      map_add, map_mul, map_pow, map_neg, map_one, map_ofNat] <;> ring

/-- `signTranslate ε (-(ε m))` undoes `signTranslate ε m`. -/
theorem signTranslate_inv {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (m : ℤ) (f : ℤ[X]) :
    signTranslate ε (-(ε * m)) (signTranslate ε m f) = f := by
  rcases hε with rfl | rfl
  · simp only [signTranslate, C_comp, comp_assoc, add_comp, X_comp, map_one, one_mul]
    rw [show X + C (-m) + C m = (X : ℤ[X]) by rw [map_neg]; ring, comp_X]
  · simp only [signTranslate, mul_comp, C_comp, comp_assoc, add_comp, X_comp]
    rw [show C (-1 : ℤ) * (C (-1 : ℤ) * (X + C (-(-1 * m))) + C m) = (X : ℤ[X]) by
      simp only [map_neg, map_one, map_mul]; ring, comp_X, ← mul_assoc, ← C_mul]
    simp

/-! ### Real roots, `n > 0`, and the height condition -/

/-- The roots of `f ∈ F_mon` are real. -/
theorem real_roots {a₂ a₁ a₀ : ℤ}
    (hc : HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ))) :
    ∃ x y z : ℝ, (a₂ : ℝ) = -(x + y + z) ∧ (a₁ : ℝ) = x * y + x * z + y * z ∧
      (a₀ : ℝ) = -(x * y * z) := by
  have hs := Cubic.Counting.CyclicPolynomialRealRoots.splits_real hc
  let Q : _root_.Cubic ℝ := ⟨1, a₂, a₁, a₀⟩
  have hQ : Q.a ≠ 0 := by norm_num [Q]
  have hs' : (Q.toPoly.map (RingHom.id ℝ)).Splits := by
    convert hs using 1
    simp [Q, _root_.Cubic.toPoly, monicCubic]
  obtain ⟨x, y, z, hr⟩ := (_root_.Cubic.splits_iff_roots_eq_three hQ).mp hs'
  refine ⟨x, y, z, ?_, ?_, ?_⟩
  · simpa [Q] using _root_.Cubic.b_eq_three_roots hQ hr
  · simpa [Q] using _root_.Cubic.c_eq_three_roots hQ hr
  · simpa [Q] using _root_.Cubic.d_eq_three_roots hQ hr

/-- `n > 0`: otherwise all three roots equal `-a₂/3`, which is rational, and `f` would split
over `ℚ`. -/
theorem invariant_pos {a₂ a₁ a₀ : ℤ}
    (hc : HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ))) :
    0 < a₂ ^ 2 - 3 * a₁ := by
  obtain ⟨x, y, z, h₂, h₁, h₀⟩ := real_roots hc
  by_contra hn
  have hR : (a₂ : ℝ) ^ 2 - 3 * a₁ ≤ 0 := by exact_mod_cast not_lt.mp hn
  rw [h₂, h₁] at hR
  have hxy : x = y := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  have hyz : y = z := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  subst hxy hyz
  -- with `t = a₂/3`, `f = (X + t)³`
  have e₁ : (a₁ : ℚ) = 3 * ((a₂ : ℚ) / 3) ^ 2 := by
    have : (3 * a₁ : ℝ) = a₂ ^ 2 := by rw [h₁, h₂]; ring
    have : (3 * a₁ : ℤ) = a₂ ^ 2 := by exact_mod_cast this
    have : (3 * a₁ : ℚ) = a₂ ^ 2 := by exact_mod_cast this
    linear_combination this / 3
  have e₀ : (a₀ : ℚ) = ((a₂ : ℚ) / 3) ^ 3 := by
    have : (27 * a₀ : ℝ) = a₂ ^ 3 := by rw [h₀, h₂]; ring
    have : (27 * a₀ : ℤ) = a₂ ^ 3 := by exact_mod_cast this
    have : (27 * a₀ : ℚ) = a₂ ^ 3 := by exact_mod_cast this
    linear_combination this / 27
  have hf : (monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ) = (X + C ((a₂ : ℚ) / 3)) ^ 3 := by
    simp only [monicCubic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    simp only [eq_intCast]
    rw [e₁, e₀]
    obtain ⟨t, ht⟩ : ∃ t : ℚ, (a₂ : ℚ) = 3 * t := ⟨(a₂ : ℚ) / 3, by ring⟩
    rw [ht, show 3 * t / 3 = t by ring]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [hf] at hc
  obtain ⟨e⟩ := hc
  letI := Gal.uniqueGalOfSplits _ ((Splits.X_add_C ((a₂ : ℚ) / 3)).pow 3)
  have := Nat.card_congr e.toEquiv
  simp at this

/-- The arithmetic–geometric mean inequality for three nonnegative reals. -/
theorem amgm {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u * v * w ≤ ((u + v + w) / 3) ^ 3 := by
  nlinarith [mul_nonneg hu (sq_nonneg (v - w)), mul_nonneg hv (sq_nonneg (u - w)),
    mul_nonneg hw (sq_nonneg (u - v)), mul_nonneg (add_nonneg (add_nonneg hu hv) hw)
      (add_nonneg (add_nonneg (sq_nonneg (u - v)) (sq_nonneg (v - w))) (sq_nonneg (u - w)))]

/-- The height condition in terms of `s = -a₂` and `n = a₂² - 3a₁`. -/
theorem height_iff {a₂ a₁ a₀ : ℤ}
    (hc : HasCyclicCubicGaloisGroup ((monicCubic a₂ a₁ a₀).map (Int.castRingHom ℚ))) (H : ℝ) :
    weightedHeight (monicCubic a₂ a₁ a₀) ≤ H ↔
      |(a₂ : ℝ)| ≤ H ∧ (a₂ : ℝ) ^ 2 - 3 * a₁ ≤ (a₂ : ℝ) ^ 2 + 3 * H ^ 2 := by
  obtain ⟨x, y, z, h₂, h₁, h₀⟩ := real_roots hc
  have hn : (0 : ℝ) < (a₂ : ℝ) ^ 2 - 3 * a₁ := by exact_mod_cast invariant_pos hc
  simp only [weightedHeight, monicCubic_coeff_two, monicCubic_coeff_one, monicCubic_coeff_zero,
    max_le_iff]
  constructor
  · rintro ⟨h2, h1, -⟩
    have hH : 0 ≤ H := (abs_nonneg _).trans h2
    have h1' := (abs_le.mp ((Real.sqrt_le_left hH).mp h1)).1
    exact ⟨h2, by linarith⟩
  · rintro ⟨h2, hn'⟩
    have hH : 0 ≤ H := (abs_nonneg _).trans h2
    have hs2 : (a₂ : ℝ) ^ 2 ≤ H ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have ha₁ : |(a₁ : ℝ)| ≤ H ^ 2 := abs_le.mpr ⟨by linarith, by nlinarith⟩
    refine ⟨h2, (Real.sqrt_le_left hH).mpr ha₁, ?_⟩
    -- `Σ rᵢ² = a₂² - 2a₁ ≤ 3H²`, so `a₀² = Π rᵢ² ≤ H⁶`
    have hsum : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 * H ^ 2 := by
      have : x ^ 2 + y ^ 2 + z ^ 2 = (a₂ : ℝ) ^ 2 - 2 * a₁ := by rw [h₂, h₁]; ring
      rw [this]; linarith [(abs_le.mp ha₁).1]
    have hsq : (a₀ : ℝ) ^ 2 ≤ (H ^ 3) ^ 2 := by
      have h := amgm (sq_nonneg x) (sq_nonneg y) (sq_nonneg z)
      have hm : ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ^ 3 ≤ (H ^ 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      calc (a₀ : ℝ) ^ 2 = x ^ 2 * y ^ 2 * z ^ 2 := by rw [h₀]; ring
        _ ≤ (H ^ 2) ^ 3 := h.trans hm
        _ = (H ^ 3) ^ 2 := by ring
    have ha₀ : |(a₀ : ℝ)| ≤ H ^ 3 := abs_le_of_sq_le_sq' hsq (by positivity) |>.elim
      (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
    calc |(a₀ : ℝ)| ^ (1 / 3 : ℝ) ≤ (H ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) ha₀ (by norm_num)
      _ = H := by
          rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast hH (by norm_num)

/-! ### The lemma -/

theorem «lemma:generalHeightReduction» :
    CubicTargets.Counting.GeneralMonic.GeneralHeightReductionClaim := by
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨⟨a₂, a₁, a₀, rfl⟩, hc⟩
    refine ⟨by simpa [invariant] using invariant_pos hc, fun H => ?_⟩
    rw [height_iff hc H]
    simp only [trace, invariant, monicCubic_coeff_two, monicCubic_coeff_one]
    push_cast
    rw [abs_neg, neg_sq]
  · intro s n ε hs hε hmod
    have hεε := sign_cases hε
    have hm : 3 * ((ε * s - 1) / 3) = ε * s - 1 := Int.mul_ediv_cancel' hmod.symm.dvd
    set m := (ε * s - 1) / 3
    refine ⟨?_, (Function.LeftInverse.injective (signTranslate_inv hε m)).injOn, ?_⟩
    · rintro f ⟨⟨⟨a₂, a₁, a₀, rfl⟩, hc⟩, htr, hinv⟩
      simp only [trace, invariant, monicCubic_coeff_two, monicCubic_coeff_one] at htr hinv
      have hb₂ : 3 * m + ε * a₂ = -1 := by linear_combination hm - ε * htr
      refine ⟨⟨⟨3 * m ^ 2 + 2 * ε * a₂ * m + a₁, m ^ 3 + ε * a₂ * m ^ 2 + a₁ * m + ε * a₀, ?_⟩,
        (cyclic_signTranslate_iff hε m (monicCubic_map_ne_zero _ _ _)).mpr hc⟩,
        ?_⟩
      · rw [signTranslate_monicCubic hε, traceOneCubic_eq, hb₂]
      · rw [signTranslate_monicCubic hε, monicCubic_coeff_one]
        linear_combination (-(3 * m + ε * a₂ - 1)) * hb₂ + a₂ ^ 2 * hεε + hinv
    · rintro g ⟨⟨⟨a, b, rfl⟩, hc⟩, hn⟩
      rw [traceOneCubic_eq] at hc hn ⊢
      rw [monicCubic_coeff_one] at hn
      have hback := signTranslate_inv hε (-(ε * m)) (monicCubic (-1) a b)
      rw [show -(ε * -(ε * m)) = m by linear_combination m * hεε] at hback
      refine ⟨_, ⟨⟨⟨_, _, _, signTranslate_monicCubic hε _ _ _ _⟩,
        (cyclic_signTranslate_iff hε _ (monicCubic_map_ne_zero _ _ _)).mpr hc⟩, ?_, ?_⟩, hback⟩
      · rw [signTranslate_monicCubic hε]
        simp only [trace, monicCubic_coeff_two]
        linear_combination ε * hm + s * hεε
      · rw [signTranslate_monicCubic hε]
        simp only [invariant, monicCubic_coeff_two, monicCubic_coeff_one]
        linear_combination hεε + hn
  · intro s n hs
    have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
    have hm : 3 * (s / 3) = s := Int.mul_ediv_cancel' hs
    set m := s / 3
    refine ⟨?_, (Function.LeftInverse.injective (signTranslate_inv hε m)).injOn, ?_⟩
    · rintro f ⟨⟨⟨a₂, a₁, a₀, rfl⟩, hc⟩, htr, hinv⟩
      simp only [trace, invariant, monicCubic_coeff_two, monicCubic_coeff_one] at htr hinv
      refine ⟨3 * m ^ 2 - a₁, m ^ 3 + 1 * a₂ * m ^ 2 + a₁ * m + 1 * a₀, ?_, ?_,
        (cyclic_signTranslate_iff hε m (monicCubic_map_ne_zero _ _ _)).mpr hc⟩
      · linear_combination -hinv + (a₂ - 3 * m) * (hm - htr)
      · rw [signTranslate_monicCubic hε]
        congr 1
        · linear_combination hm - htr
        · linear_combination 2 * m * (hm - htr)
    · rintro g ⟨N, c, hnN, rfl, hc⟩
      have hback := signTranslate_inv hε (-(1 * m)) (monicCubic 0 (-N) c)
      rw [show -(1 * -(1 * m)) = m by ring] at hback
      refine ⟨_, ⟨⟨⟨_, _, _, signTranslate_monicCubic hε _ _ _ _⟩,
        (cyclic_signTranslate_iff hε _ (monicCubic_map_ne_zero _ _ _)).mpr hc⟩, ?_, ?_⟩, hback⟩
      · rw [signTranslate_monicCubic hε]
        simp only [trace, monicCubic_coeff_two]
        linear_combination hm
      · rw [signTranslate_monicCubic hε]
        simp only [invariant, monicCubic_coeff_two, monicCubic_coeff_one]
        linear_combination -hnN

end Cubic.Counting.GeneralHeightReduction
