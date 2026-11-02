import Cubic.PoissonSummation.IntegralHeightIndex

/-!
# The actual height on integral rational points

All finite `D₀` factors are one on the original integral cutoff. The complex
place then gives `H(P,sD₀) = index(P)^(s/2)`. This identifies the previously
defined height fibers with integer-index fibers; it does not define a height
by the formula to be proved. The factor one-half comes from the original
norm character and its complex absolute value.
-/

noncomputable section

namespace Cubic.PoissonSummation.IntegralHeightNormalization

open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct QuotientLocalFourier QuotientFiniteHeight
open RationalAdelicEmbedding AdelicHeightZetaData IntegralHeightIndex
open ArchimedeanQuotientLogarithm (coordinate)

theorem local_inverseHeight_one (p : Nat.Primes) (s : ℂ) :
    ∀ x ∈ (family p).integralLocus, (family p).inverseHeight s 0 x = 1 := by
  apply FiniteAdelicData.localLogarithm_induction
    (fun D _ => ∀ x ∈ D.integralLocus, D.inverseHeight s 0 x = 1)
  · intro p x hx
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
    have h := (QuotientInvariantIntegrality.split_mem_iff p.1 x).mp hx
    rw [SplitLocalIntegrality.coefficientLocus_eq_integralLocus p.1 (by
      intro he; have := p.2; simp [he] at this)] at h
    change splitInverseHeight p.1 s 0 x = 1
    rw [splitInverseHeight_eq, SplitLocalModel.inverseHeight_on_cone _ _ _ _ h]
    simp
  · intro p x hx
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩
    have h := (QuotientInvariantIntegrality.inert_mem_iff p.1 x).mp hx
    rw [InertLocalIntegrality.coefficientLocus_eq_integralLocus] at h
    change inertInverseHeight p.1 s 0 x = 1
    rw [inertInverseHeight_eq, InertLocalModel.inverseHeight_on_cone _ _ _ _ h]
    simp
  · intro x hx
    have h := (QuotientInvariantIntegrality.ramified_mem_iff x).mp hx
    rw [RamifiedLocalIntegrality.coefficientLocus_eq_integralLocus] at h
    change ramifiedInverseHeight s 0 x = 1
    rw [ramifiedInverseHeight_eq]
    exact RamifiedLocalModel.inverseHeight_on_compactUnits s 0 _
      (RamifiedLocalModel.integralLocus_subset h)

theorem finite_inverseHeight_one (P : IntegralRationalPoints) (s : ℂ) :
    FiniteAdelicData.inverseHeight s 0 (finiteDiagonal P.val) = 1 := by
  unfold FiniteAdelicData.inverseHeight
  calc
    _ = ∏' _ : Nat.Primes, (1 : ℂ) := tprod_congr fun p =>
      local_inverseHeight_one p s _ (P.property p)
    _ = 1 := tprod_one

theorem coordinate_eq_half_log (P : IntegralRationalPoints) :
    coordinate (baseChange ℝ P.val) = Real.log (index P) / 2 := by
  have h := QuotientNormLogarithm.infinite_value (baseChange ℝ P.val)
  rw [AdelicRationalCharacter.norm_baseChange, norm_value_eq_index, eq_ratCast,
    Rat.cast_natCast] at h
  have hl := congrArg Real.log h
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  dsimp [coordinate]
  linarith

theorem coordinate_nonneg (P : IntegralRationalPoints) :
    0 ≤ coordinate (baseChange ℝ P.val) := by
  rw [coordinate_eq_half_log]
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast index_pos P)) (by norm_num)

theorem height_eq_exp (P : IntegralRationalPoints) (s : ℂ) :
    height s 0 (diagonal P.val) =
      Complex.exp (s * (coordinate (baseChange ℝ P.val) : ℂ)) := by
  change ArchimedeanQuotientLogarithm.inverseHeight (-s) (-0) (baseChange ℝ P.val) *
    FiniteAdelicData.inverseHeight (-s) (-0) (finiteDiagonal P.val) = _
  rw [neg_zero, finite_inverseHeight_one, mul_one, ArchimedeanQuotientLogarithm.inverseHeight_eq]
  congr 1
  simp [supportFunction, min_eq_right (neg_nonpos.mpr (coordinate_nonneg P))]

theorem height_eq_cpow_index (P : IntegralRationalPoints) (s : ℂ) :
    height s 0 (diagonal P.val) = (index P : ℂ) ^ (s / 2) := by
  rw [height_eq_exp, Complex.cpow_def_of_ne_zero (by exact_mod_cast (index_pos P).ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    coordinate_eq_half_log]
  congr 1
  push_cast
  ring

theorem pointHeight_eq_sqrt_index (P : IntegralRationalPoints) :
    HeightCountingData.pointHeight P = (Real.sqrt (index P) : ℂ) := by
  change height 1 0 (diagonal P.val) = _
  rw [height_eq_exp, one_mul]
  have hpos := norm_pos_iff.mpr (CyclotomicArchimedean.pointEquiv (baseChange ℝ P.val)).ne_zero
  rw [coordinate, ← Complex.ofReal_exp, Real.exp_log hpos]
  apply congrArg Complex.ofReal
  have h := QuotientNormLogarithm.infinite_value (baseChange ℝ P.val)
  rw [AdelicRationalCharacter.norm_baseChange, norm_value_eq_index, eq_ratCast,
    Rat.cast_natCast] at h
  rw [h, Real.sqrt_sq (norm_nonneg _)]

theorem zetaTerm_eq (P : IntegralRationalPoints) (s : ℂ) :
    zetaTerm s 0 P = (index P : ℂ) ^ (-(s / 2)) := by
  rw [zetaTerm, height_eq_cpow_index, Complex.cpow_neg]

end Cubic.PoissonSummation.IntegralHeightNormalization
