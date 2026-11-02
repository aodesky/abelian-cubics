import Cubic.BoxHeight.ConductorSumAlternating
import Cubic.PoissonSummation.LeadingTermsAssembly
import Cubic.PoissonSummation.QuadraticDedekindFactorization
import Cubic.PoissonSummation.QuadraticDedekindResidue

/-!
# `L₁ = L(1, χ) = π/(3√3)`

For real `s ∈ [1, 2]` put `F(s) = Σ_{k ≥ 0} ((3k+1)^{-s} - (3k+2)^{-s})`. Each term lies in
`[0, s(3k+1)^{-s-1}] ⊆ [0, 2/(k+1)²]` (from `(1+t)^{-s} ≥ 1 - s log(1+t) ≥ 1 - st`), so by the
Weierstrass M-test `F` is continuous on `[1, 2]`, and `F(1) = L₁`.

For `s > 1` the Dirichlet series of `χ` converges absolutely, and grouping it by residue
classes mod `3` shows `L(s, χ) = F(s)`. Since mathlib's `LFunction χ` is entire (`χ` is
nontrivial), letting `s → 1⁺` gives `L(1, χ) = F(1) = L₁`. The project identifies
`L(1, χ)` with the residue `π/(3√3)` of the Dedekind zeta function of `ℚ(√-3)`.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open Filter
open scoped Topology
open Cubic.PoissonSummation

/-- `(3k+1)^{-s} - (3k+2)^{-s}`. -/
def uTerm (s : ℝ) (k : ℕ) : ℝ := (3 * (k : ℝ) + 1) ^ (-s) - (3 * (k : ℝ) + 2) ^ (-s)

/-- `F(s) = Σ_k ((3k+1)^{-s} - (3k+2)^{-s})`. -/
def Fser (s : ℝ) : ℝ := ∑' k : ℕ, uTerm s k

theorem uTerm_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : 0 ≤ uTerm s k := by
  rw [uTerm, sub_nonneg]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

/-- `(x+1)^{-s} ≥ x^{-s} (1 - s/x)` for `x > 0`, `s ≥ 0`. -/
theorem rpow_succ_lower {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    x ^ (-s) * (1 - s / x) ≤ (x + 1) ^ (-s) := by
  have hx1 : x + 1 = x * (1 + 1 / x) := by field_simp
  have ht : 0 < 1 + 1 / x := by positivity
  rw [hx1, Real.mul_rpow hx.le ht.le]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos ht]
  have hlog : Real.log (1 + 1 / x) ≤ 1 / x := by
    have := Real.log_le_sub_one_of_pos ht; linarith
  have := Real.add_one_le_exp (Real.log (1 + 1 / x) * -s)
  have : s * Real.log (1 + 1 / x) ≤ s * (1 / x) := mul_le_mul_of_nonneg_left hlog hs
  rw [div_eq_mul_one_div s x]
  nlinarith

theorem uTerm_le {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (k : ℕ) :
    uTerm s k ≤ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
  set x : ℝ := 3 * (k : ℝ) + 1 with hxdef
  have hx1 : 1 ≤ x := by simp only [hxdef]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hx : 0 < x := by linarith
  have hlow := rpow_succ_lower hx (by linarith : (0 : ℝ) ≤ s)
  have hx2 : 3 * (k : ℝ) + 2 = x + 1 := by simp only [hxdef]; ring
  rw [uTerm, ← hxdef, hx2]
  have hpow : x ^ (-s) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hpos : 0 ≤ x ^ (-s) := by positivity
  have hkx : (k : ℝ) + 1 ≤ x := by simp only [hxdef]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- `x^{-s} - (x+1)^{-s} ≤ x^{-s} s / x ≤ 2 / x² ≤ 2 / (k+1)²`
  have h1 : x ^ (-s) - (x + 1) ^ (-s) ≤ x ^ (-s) * (s / x) := by nlinarith
  have h2 : x ^ (-s) * (s / x) ≤ x⁻¹ * (2 / x) :=
    mul_le_mul hpow (div_le_div_of_nonneg_right hs2 hx.le) (by positivity) (by positivity)
  have h3 : x⁻¹ * (2 / x) ≤ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [inv_mul_eq_div, div_div, ← sq, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hk0.le hkx 2)
  linarith

theorem summable_majorant : Summable (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
  have := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
  exact (by simpa [Function.comp_def] using this : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2)).mul_left 2

theorem continuous_uTerm (k : ℕ) : Continuous (fun s : ℝ => uTerm s k) := by
  unfold uTerm
  refine (continuous_const.rpow continuous_neg fun _ => Or.inl ?_).sub
    (continuous_const.rpow continuous_neg fun _ => Or.inl ?_) <;> positivity

theorem continuousOn_Fser : ContinuousOn Fser (Set.Icc 1 2) := by
  refine continuousOn_tsum (fun k => (continuous_uTerm k).continuousOn) summable_majorant ?_
  intro k s hs
  rw [Real.norm_of_nonneg (uTerm_nonneg (by linarith [hs.1]) k)]
  exact uTerm_le hs.1 hs.2 k

theorem Fser_one : Fser 1 = L₁ := by
  simp [Fser, uTerm, L₁, Real.rpow_neg_one]

theorem character_nat (n : ℕ) : QuadraticDirichletCharacter.character (n : ZMod 3) = (chi n : ℂ) := by
  rw [QuadraticDirichletCharacter.character_of_mod]
  rcases mod_three_cases n with h | h | h <;> simp [h, chi]

/-- For real `s > 1`, `L(s, χ) = F(s)`. -/
theorem LFunction_eq_Fser {s : ℝ} (hs : 1 < s) :
    DirichletCharacter.LFunction QuadraticDirichletCharacter.character (s : ℂ) = (Fser s : ℂ) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs', LSeries]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re
    QuadraticDirichletCharacter.character hs'
  rw [Nat.sumByResidueClasses hsum 3]
  set t := LSeries.term (fun n : ℕ => QuadraticDirichletCharacter.character n) (s : ℂ)
  have hj : ∀ j : ℕ, Summable (fun m : ℕ => t (j + 3 * m)) := fun j =>
    hsum.comp_injective (fun a c hac => by
      have : j + 3 * a = j + 3 * c := hac
      omega)
  have huniv : ∑ j : ZMod 3, ∑' m : ℕ, t (j.val + 3 * m) =
      ∑' m : ℕ, t (0 + 3 * m) + ∑' m : ℕ, t (1 + 3 * m) + ∑' m : ℕ, t (2 + 3 * m) := by
    exact Fin.sum_univ_three (fun j : Fin 3 => ∑' m : ℕ, t ((j : ℕ) + 3 * m))
  rw [huniv, ← (hj 0).tsum_add (hj 1), ← ((hj 0).add (hj 1)).tsum_add (hj 2), Fser,
    Complex.ofReal_tsum]
  congr 1
  funext m
  have hc : ∀ n : ℕ, n ≠ 0 → t n = (chi n : ℂ) / (n : ℂ) ^ (s : ℂ) := fun n hn => by
    simp only [t, LSeries.term_of_ne_zero hn, character_nat]
  have h0 : t (0 + 3 * m) = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [t]
    rw [hc _ (by omega)]
    have : chi (3 * m) = 0 := by simp [chi, Nat.mul_mod_right]
    simp [this]
  have h1 : chi (1 + 3 * m) = 1 := by simp [chi, Nat.add_mul_mod_self_left]
  have h2 : chi (2 + 3 * m) = -1 := by simp [chi, Nat.add_mul_mod_self_left]
  rw [h0, hc _ (by omega), hc _ (by omega), h1, h2, uTerm, Complex.ofReal_sub,
    Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
  push_cast
  rw [Complex.cpow_neg, Complex.cpow_neg]
  ring_nf

/-- `L₁ = L(1, χ)`. -/
theorem L₁_eq_LFunction :
    (L₁ : ℂ) = DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 := by
  have hφ : Tendsto (fun s : ℝ => DirichletCharacter.LFunction
      QuadraticDirichletCharacter.character (s : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1)) := by
    have hc := (QuadraticDirichletCharacter.differentiable_LFunction.continuous.comp
      Complex.continuous_ofReal).tendsto 1
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hψ : Tendsto (fun s : ℝ => (Fser s : ℂ)) (𝓝[>] 1) (𝓝 (Fser 1 : ℂ)) := by
    have hw : ContinuousWithinAt Fser (Set.Ioi 1) 1 :=
      (continuousOn_Fser 1 ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT (by norm_num))
    exact (Complex.continuous_ofReal.tendsto _).comp hw.tendsto
  rw [← Fser_one]
  refine tendsto_nhds_unique hψ (hφ.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact LFunction_eq_Fser hs

/-- `L₁ = π/(3√3)`. -/
theorem L₁_eq : L₁ = Real.pi / (3 * Real.sqrt 3) := by
  have h := L₁_eq_LFunction
  rw [LeadingTermsAssembly.L_one_eq_residue QuadraticDedekindFactorization.factorization,
    QuadraticDedekindResidue.residue_value] at h
  exact_mod_cast h

end Cubic.BoxHeight.ConductorSum
