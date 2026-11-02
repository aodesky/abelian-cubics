import Cubic.SurfaceGeometry.IntegralInvariantNormalForm
import Cubic.ToricHeights.AffineC3Invariants
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.ZMod.Basic

/-! Degree modulo three on the original invariant ring and on its freely
generated symmetric coefficient ring. The zero component is the third Veronese. -/

noncomputable section

namespace Cubic.SurfaceGeometry.VeroneseGrading

open MvPolynomial InvariantCubicData Cubic.ToricHeights.TernaryCyclicInvariants

def ordinaryWeight : Fin 3 → ZMod 3 := fun _ => 1
def symmetricWeight : Fin 3 → ZMod 3 := fun i => i.val + 1

theorem e_homogeneous (i : Fin 3) :
    IsWeightedHomogeneous ordinaryWeight (e (i.val + 1)) (symmetricWeight i) := by
  have hx (j : Fin 3) := isWeightedHomogeneous_X (R := ℤ) ordinaryWeight j
  fin_cases i
  · rw [Cubic.ToricHeights.AffineC3Invariants.esymm_one]
    exact ((hx 0).add (hx 1)).add (hx 2)
  · rw [Cubic.ToricHeights.AffineC3Invariants.esymm_two]
    exact (((hx 0).mul (hx 1)).add ((hx 0).mul (hx 2))).add ((hx 1).mul (hx 2))
  · rw [Cubic.ToricHeights.AffineC3Invariants.esymm_three]
    exact ((hx 0).mul (hx 1)).mul (hx 2)

theorem delta_homogeneous : IsWeightedHomogeneous ordinaryWeight delta 0 := by
  have hx (j : Fin 3) := isWeightedHomogeneous_X (R := ℤ) ordinaryWeight j
  unfold delta
  have h₁ := ((hx 0).pow 2).mul (hx 1)
  have h₂ := ((hx 1).pow 2).mul (hx 2)
  have h₃ := ((hx 2).pow 2).mul (hx 0)
  have hc : (2 : ℕ) • (1 : ZMod 3) + 1 = 0 := by decide
  simpa only [ordinaryWeight, hc] using (h₁.add h₂).add h₃

theorem symmetric_monomial_homogeneous (d : Fin 3 →₀ ℕ) (r : ℤ) :
    IsWeightedHomogeneous ordinaryWeight (symmetricEval (monomial d r))
      (Finsupp.weight symmetricWeight d) := by
  rw [symmetricEval, aeval_monomial]
  have hh := IsWeightedHomogeneous.prod d.support
    (fun i => e (i.val + 1) ^ d i) (fun i => d i • symmetricWeight i)
    (fun i _ => (e_homogeneous i).pow (d i))
  simpa [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
    Algebra.smul_def, MvPolynomial.algebraMap_eq] using hh.C_mul r

theorem component_symmetricEval (k : ZMod 3) (p : SymmetricCoefficients) :
    weightedHomogeneousComponent ordinaryWeight k (symmetricEval p) =
      symmetricEval (weightedHomogeneousComponent symmetricWeight k p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d r =>
    rw [weightedHomogeneousComponent_of_mem (symmetric_monomial_homogeneous d r),
      weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial symmetricWeight d r rfl)]
    split_ifs <;> simp

theorem component_symmetricEval_delta (k : ZMod 3) (p : SymmetricCoefficients) :
    weightedHomogeneousComponent ordinaryWeight k (symmetricEval p * delta) =
      symmetricEval (weightedHomogeneousComponent symmetricWeight k p) * delta := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]
  | monomial d r =>
    have hh : IsWeightedHomogeneous ordinaryWeight (symmetricEval (monomial d r) * delta)
        (Finsupp.weight symmetricWeight d) := by
      simpa only [add_zero] using (symmetric_monomial_homogeneous d r).mul delta_homogeneous
    rw [weightedHomogeneousComponent_of_mem hh,
      weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial symmetricWeight d r rfl)]
    split_ifs <;> simp

theorem component_normalForm (k : ZMod 3) (p : SymmetricCoefficients × SymmetricCoefficients) :
    weightedHomogeneousComponent ordinaryWeight k (normalForm p) =
      normalForm (weightedHomogeneousComponent symmetricWeight k p.1,
        weightedHomogeneousComponent symmetricWeight k p.2) := by
  simp only [normalForm, map_add, component_symmetricEval, component_symmetricEval_delta]

theorem symmetricEval_homogeneous {p : SymmetricCoefficients} {k : ZMod 3}
    (hp : IsWeightedHomogeneous symmetricWeight p k) :
    IsWeightedHomogeneous ordinaryWeight (symmetricEval p) k := by
  have h := weightedHomogeneousComponent_isWeightedHomogeneous (w := ordinaryWeight) k
    (symmetricEval p)
  rw [component_symmetricEval, hp.weightedHomogeneousComponent_same] at h
  exact h

theorem normalForm_homogeneous_iff (p : SymmetricCoefficients × SymmetricCoefficients) :
    IsWeightedHomogeneous ordinaryWeight (normalForm p) 0 ↔
      IsWeightedHomogeneous symmetricWeight p.1 0 ∧
        IsWeightedHomogeneous symmetricWeight p.2 0 := by
  constructor
  · intro hp
    have hc (k : ZMod 3) (hk : k ≠ 0) :
        weightedHomogeneousComponent symmetricWeight k p.1 = 0 ∧
          weightedHomogeneousComponent symmetricWeight k p.2 = 0 := by
      have he : normalForm (weightedHomogeneousComponent symmetricWeight k p.1,
          weightedHomogeneousComponent symmetricWeight k p.2) = normalForm (0,0) := by
        rw [← component_normalForm, hp.weightedHomogeneousComponent_ne k hk]
        simp [normalForm]
      have he' := IntegralInvariantNormalForm.normalForm_injective he
      exact ⟨congrArg Prod.fst he', congrArg Prod.snd he'⟩
    constructor
    · intro d hd
      by_contra hn
      have he := congrArg (coeff d) (hc (Finsupp.weight symmetricWeight d) hn).1
      simp only [coeff_weightedHomogeneousComponent, coeff_zero] at he
      exact hd he
    · intro d hd
      by_contra hn
      have he := congrArg (coeff d) (hc (Finsupp.weight symmetricWeight d) hn).2
      simp only [coeff_weightedHomogeneousComponent, coeff_zero] at he
      exact hd he
  · rintro ⟨hp,hq⟩
    exact (symmetricEval_homogeneous hp).add
      (by simpa only [add_zero] using (symmetricEval_homogeneous hq).mul delta_homogeneous)

end Cubic.SurfaceGeometry.VeroneseGrading
