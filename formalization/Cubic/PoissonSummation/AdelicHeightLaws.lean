import Cubic.PoissonSummation.AdelicHeightZetaData
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Absolute values and reciprocals of the actual adelic height

These identities justify replacing complex parameters by their real parts in
the paper's nonnegative integration argument. They hold before the cutoff,
on every cone of the support function.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicHeightLaws

open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct QuotientLocalFourier
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

theorem supportFunction_realPart (s₀ σ : ℂ) (n : ℝ × ℝ) :
    supportFunction s₀.re σ.re n = ((supportFunction s₀ σ n).re : ℂ) := by
  apply Complex.ext <;> simp [supportFunction, Complex.mul_re]

theorem norm_support_cpow (p : ℕ) (hp : 0 < p) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    (‖(p : ℂ) ^ supportFunction s₀ σ n‖ : ℂ) =
      (p : ℂ) ^ supportFunction s₀.re σ.re n := by
  rw [Complex.norm_natCast_cpow_of_pos hp, supportFunction_realPart,
    Complex.ofReal_cpow (Nat.cast_nonneg p)]
  rfl

theorem local_norm_inverseHeight (p : Nat.Primes) (s₀ σ : ℂ) :
    ∀ x : (family p).Carrier,
      (‖(family p).inverseHeight s₀ σ x‖ : ℂ) = (family p).inverseHeight s₀.re σ.re x := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    intro x
    change (‖QuotientFiniteHeight.splitInverseHeight p s₀ σ x‖ : ℂ) = _
    simp only [splitData, QuotientFiniteHeight.splitInverseHeight_eq, SplitLocalModel.inverseHeight]
    exact norm_support_cpow p p.2.pos s₀ σ _
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    intro x
    change (‖QuotientFiniteHeight.inertInverseHeight p s₀ σ x‖ : ℂ) = _
    simp only [inertData, QuotientFiniteHeight.inertInverseHeight_eq, InertLocalModel.inverseHeight]
    exact norm_support_cpow p p.2.pos s₀ σ _
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    intro x
    change (‖QuotientFiniteHeight.ramifiedInverseHeight s₀ σ x‖ : ℂ) = _
    simp only [ramifiedData, QuotientFiniteHeight.ramifiedInverseHeight_eq, RamifiedLocalModel.inverseHeight]
    exact norm_support_cpow 3 (by decide) s₀ σ _

theorem infinite_norm_inverseHeight (s₀ σ : ℂ) (x : ArchimedeanHaarData.Points) :
    (‖ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x‖ : ℂ) =
      ArchimedeanQuotientLogarithm.inverseHeight s₀.re σ.re x := by
  simp only [ArchimedeanQuotientLogarithm.inverseHeight_eq, Complex.norm_exp,
    supportFunction_realPart, Complex.ofReal_exp]

theorem finite_norm_inverseHeight (s₀ σ : ℂ) (x : FiniteAdelicData.Points) :
    (‖FiniteAdelicData.inverseHeight s₀ σ x‖ : ℂ) =
      FiniteAdelicData.inverseHeight s₀.re σ.re x := by
  classical
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.property
  have hS : ∀ p ∉ hfin.toFinset, x p ∈ (family p).maxCompact := by
    intro p hp
    by_contra hn
    exact hp (hfin.mem_toFinset.mpr hn)
  rw [FiniteAdelicData.inverseHeight_eq_prod s₀ σ x _ hS,
    FiniteAdelicData.inverseHeight_eq_prod s₀.re σ.re x _ hS]
  simp only [norm_prod, Complex.ofReal_prod, local_norm_inverseHeight]

/-- The absolute-value identity used before applying Tonelli and monotone convergence. -/
theorem norm_inverseHeight (s₀ σ : ℂ) (x : AdelicData.Points) :
    (‖AdelicData.inverseHeight s₀ σ x‖ : ℂ) = AdelicData.inverseHeight s₀.re σ.re x := by
  simp only [AdelicData.inverseHeight, norm_mul, Complex.ofReal_mul,
    infinite_norm_inverseHeight, finite_norm_inverseHeight]

theorem norm_cutoffHeight (s₀ σ : ℂ) (x : AdelicData.Points) :
    (‖AdelicHeightZetaData.cutoffHeight s₀ σ x‖ : ℂ) =
      AdelicHeightZetaData.cutoffHeight s₀.re σ.re x := by
  classical
  by_cases hx : x ∈ AdelicHeightZetaData.integralLocus
  · simp only [AdelicHeightZetaData.cutoffHeight, Set.indicator_of_mem hx, norm_inverseHeight]
  · simp only [AdelicHeightZetaData.cutoffHeight, Set.indicator_of_notMem hx, norm_zero,
      Complex.ofReal_zero]

theorem local_inverseHeight_neg (p : Nat.Primes) (s₀ σ : ℂ) :
    ∀ x : (family p).Carrier,
      (family p).inverseHeight (-s₀) (-σ) x = ((family p).inverseHeight s₀ σ x)⁻¹ := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    intro x
    simp only [splitData, QuotientFiniteHeight.splitInverseHeight_eq,
      SplitLocalModel.inverseHeight, supportFunction_neg, Complex.cpow_neg]
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    intro x
    simp only [inertData, QuotientFiniteHeight.inertInverseHeight_eq,
      InertLocalModel.inverseHeight, supportFunction_neg, Complex.cpow_neg]
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    intro x
    simp only [ramifiedData, QuotientFiniteHeight.ramifiedInverseHeight_eq,
      RamifiedLocalModel.inverseHeight, supportFunction_neg, Complex.cpow_neg]

theorem finite_inverseHeight_neg (s₀ σ : ℂ) (x : FiniteAdelicData.Points) :
    FiniteAdelicData.inverseHeight (-s₀) (-σ) x = (FiniteAdelicData.inverseHeight s₀ σ x)⁻¹ := by
  classical
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.property
  have hS : ∀ p ∉ hfin.toFinset, x p ∈ (family p).maxCompact := by
    intro p hp
    by_contra hn
    exact hp (hfin.mem_toFinset.mpr hn)
  rw [FiniteAdelicData.inverseHeight_eq_prod (-s₀) (-σ) x _ hS,
    FiniteAdelicData.inverseHeight_eq_prod s₀ σ x _ hS]
  simp only [local_inverseHeight_neg, Finset.prod_inv_distrib]

theorem inverseHeight_neg (s₀ σ : ℂ) (x : AdelicData.Points) :
    AdelicData.inverseHeight (-s₀) (-σ) x = (AdelicData.inverseHeight s₀ σ x)⁻¹ := by
  simp only [AdelicData.inverseHeight, ArchimedeanQuotientLogarithm.inverseHeight_eq,
    supportFunction_neg, Complex.exp_neg, finite_inverseHeight_neg, mul_inv_rev, mul_comm]

/-- The independently defined positive height has the required reciprocal. -/
theorem inverseHeight_eq_reciprocal (s₀ σ : ℂ) (x : AdelicData.Points) :
    AdelicData.inverseHeight s₀ σ x = (AdelicHeightZetaData.height s₀ σ x)⁻¹ := by
  rw [AdelicHeightZetaData.height, inverseHeight_neg, inv_inv]

end Cubic.PoissonSummation.AdelicHeightLaws
