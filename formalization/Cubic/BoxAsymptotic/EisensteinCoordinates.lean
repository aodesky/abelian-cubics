import Cubic.BoxAsymptotic.CubeDecomposition
import CubicTargets.BoxAsymptotic.Statement

/-!
# `ℤ[ζ]` in coordinates

`(a, b) ↔ a + bζ`, with norm `a² - ab + b²`, product
`(a + bζ)(c + dζ) = (ac - bd) + (ad + bc - bd)ζ`, and complex embedding `eis`. The cube
decomposition of `CubeDecomposition` in these coordinates: if `N β = n³` with `n > 0`, then
`β = u · N(γ)γ · g³ δ₀³` with `N u = 1`, `g ≥ 1`, and `γ, δ₀` primitive vectors.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.EisensteinCoordinates

open CubicTargets.BoxAsymptotic (eis)
open Cubic.Counting.EisensteinNormCount (coord coord_injective coord_surjective norm_coord
  zetaInteger_sq normForm_nonneg)
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.CubeDecomposition

/-- The norm `N(a + bζ) = a² - ab + b²`. -/
def nrm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2

/-- The product in `ℤ[ζ]`. -/
def mulE (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1 - p.2 * q.2)

theorem nrm_nonneg (p : ℤ × ℤ) : 0 ≤ nrm p := normForm_nonneg p.1 p.2

theorem nrm_mulE (p q : ℤ × ℤ) : nrm (mulE p q) = nrm p * nrm q := by
  simp only [nrm, mulE]; ring

theorem nrm_smul (k : ℤ) (p : ℤ × ℤ) : nrm (k • p) = k ^ 2 * nrm p := by
  simp only [nrm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem nrm_eq_zero {p : ℤ × ℤ} : nrm p = 0 ↔ p = 0 := by
  constructor
  · intro h
    simp only [nrm] at h
    have h1 : p.2 = 0 := by nlinarith [sq_nonneg (2 * p.1 - p.2), sq_nonneg p.2]
    have h2 : p.1 = 0 := by rw [h1] at h; nlinarith
    exact Prod.ext h2 h1
  · rintro rfl; simp [nrm]

theorem coord_mulE (p q : ℤ × ℤ) : coord (mulE p q) = coord p * coord q := by
  simp only [coord, mulE]; push_cast
  linear_combination (-(p.2 * q.2 : Integers)) * zetaInteger_sq

theorem coord_smul (k : ℤ) (p : ℤ × ℤ) : coord (k • p) = k * coord p := by
  simp only [coord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; push_cast; ring

theorem norm_coord' (p : ℤ × ℤ) : Algebra.norm ℤ (coord p) = nrm p := norm_coord p

theorem sqrt3_mul : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem eis_mulE (p q : ℤ × ℤ) : eis (mulE p q) = eis p * eis q := by
  apply Complex.ext
  · simp only [eis, mulE, Complex.mul_re]; push_cast
    linear_combination ((p.2 : ℝ) * q.2 / 4) * sqrt3_mul
  · simp only [eis, mulE, Complex.mul_im]; push_cast; ring

theorem eis_smul (k : ℤ) (p : ℤ × ℤ) : eis (k • p) = (k : ℝ) * eis p := by
  apply Complex.ext
  · simp [eis]; ring
  · simp [eis]; ring

theorem normSq_eis (p : ℤ × ℤ) : Complex.normSq (eis p) = nrm p := by
  simp only [Complex.normSq_apply, eis, nrm]; push_cast
  linear_combination ((p.2 : ℝ) ^ 2 / 4) * sqrt3_mul

theorem norm_eis_sq (p : ℤ × ℤ) : ‖eis p‖ ^ 2 = nrm p := by
  rw [Complex.sq_norm, normSq_eis]

theorem eis_injective : Function.Injective eis := by
  intro p q h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [eis] at hre him
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have h2 : (p.2 : ℝ) = q.2 := by
    have := mul_right_cancel₀ h3 (by linarith : (p.2 : ℝ) * Real.sqrt 3 = q.2 * Real.sqrt 3)
    exact this
  have h1 : (p.1 : ℝ) = q.1 := by linarith
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

theorem eis_ne_zero {p : ℤ × ℤ} (hp : p ≠ 0) : eis p ≠ 0 := by
  intro h
  have := normSq_eis p
  rw [h, map_zero] at this
  exact hp (nrm_eq_zero.mp (by exact_mod_cast this.symm))

/-- The explicit product `u · (N γ) γ · g³ δ₀³`. -/
def assemble (u γ δ₀ : ℤ × ℤ) (g : ℕ) : ℤ × ℤ :=
  mulE (mulE u (nrm γ • γ)) (((g : ℤ) ^ 3) • mulE δ₀ (mulE δ₀ δ₀))

theorem eis_assemble (u γ δ₀ : ℤ × ℤ) (g : ℕ) :
    eis (assemble u γ δ₀ g) =
      eis u * (((nrm γ : ℝ) * (g : ℝ) ^ 3 : ℝ) : ℂ) * (eis γ * eis δ₀ ^ 3) := by
  rw [assemble, eis_mulE, eis_mulE, eis_smul, eis_smul, eis_mulE, eis_mulE]
  push_cast; ring

/-- **Cube decomposition in coordinates.** -/
theorem decomposition {β : ℤ × ℤ} {n : ℕ} (hn : 0 < n) (hβ : nrm β = (n : ℤ) ^ 3) :
    ∃ (u γ δ₀ : ℤ × ℤ) (g : ℕ), nrm u = 1 ∧ Int.gcd γ.1 γ.2 = 1 ∧ Int.gcd δ₀.1 δ₀.2 = 1 ∧
      0 < g ∧ (n : ℤ) = nrm γ * (g : ℤ) ^ 2 * nrm δ₀ ∧ β = assemble u γ δ₀ g := by
  have hmul : coord β * τ (coord β) = ((n : ℤ) : Integers) ^ 3 := by
    rw [mul_τ, norm_coord', hβ]; push_cast; ring
  obtain ⟨U, γO, δO, hγ0, hdec, hprim⟩ :=
    CubeDecomposition.decomposition hmul (by exact_mod_cast hn.ne')
  obtain ⟨u, hu⟩ := coord_surjective (U : Integers)
  obtain ⟨γ, rfl⟩ := coord_surjective γO
  obtain ⟨δ, rfl⟩ := coord_surjective δO
  -- `u` is a unit
  have hnu : nrm u = 1 := by
    have h1 := (U.isUnit.map (Algebra.norm ℤ))
    rw [← hu, norm_coord'] at h1
    rcases Int.isUnit_iff.mp h1 with h | h
    · exact h
    · linarith [nrm_nonneg u]
  -- `γ` is primitive
  have hγ : Int.gcd γ.1 γ.2 = 1 := by
    set k := Int.gcd γ.1 γ.2
    have hk : ((k : ℤ) : Integers) ∣ coord γ := by
      refine ⟨coord (γ.1 / k, γ.2 / k), ?_⟩
      rw [← coord_smul]
      congr 1
      ext
      · simp only [Prod.smul_fst, smul_eq_mul]
        exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left γ.1 γ.2)).symm
      · simp only [Prod.smul_snd, smul_eq_mul]
        exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right γ.1 γ.2)).symm
    rcases Int.isUnit_iff.mp (hprim k hk) with h | h
    · exact_mod_cast h
    · omega
  -- `δ = g δ₀`
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have hβ0 : coord β = 0 := by
      rw [hdec]; simp [coord]
    have := norm_coord' β
    rw [hβ0, Algebra.norm_zero, hβ] at this
    have : (n : ℤ) ^ 3 = 0 := this.symm
    exact hn.ne' (by exact_mod_cast pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this)
  set g := Int.gcd δ.1 δ.2 with hg
  have hgpos : 0 < g := by
    rw [hg, Int.gcd_pos_iff]
    by_contra h
    push_neg at h
    exact hδ0 (Prod.ext h.1 h.2)
  set δ₀ : ℤ × ℤ := (δ.1 / g, δ.2 / g) with hδ₀def
  have hδ : δ = (g : ℤ) • δ₀ := by
    ext
    · simp only [hδ₀def, Prod.smul_fst, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left δ.1 δ.2)).symm
    · simp only [hδ₀def, Prod.smul_snd, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right δ.1 δ.2)).symm
  have hδ₀ : Int.gcd δ₀.1 δ₀.2 = 1 := Int.gcd_div_gcd_div_gcd hgpos
  have hβeq : β = assemble u γ δ₀ g := by
    apply coord_injective
    rw [hdec, mul_τ, norm_coord', hδ, coord_smul, assemble, coord_mulE, coord_mulE, coord_smul,
      coord_smul, coord_mulE, coord_mulE, hu]
    push_cast; ring
  refine ⟨u, γ, δ₀, g, hnu, hγ, hδ₀, hgpos, ?_, hβeq⟩
  have hN := hβ
  rw [hβeq, assemble, nrm_mulE, nrm_mulE, nrm_smul, nrm_smul, nrm_mulE, nrm_mulE, hnu] at hN
  have h0 := nrm_nonneg γ
  have h1 := nrm_nonneg δ₀
  refine ((pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_)
  rw [← hN]; ring

end Cubic.BoxAsymptotic.EisensteinCoordinates
