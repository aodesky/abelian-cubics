import Cubic.SurfaceGeometry.IntegralInvariantNormalForm
import Cubic.SurfaceGeometry.SurfaceInvariantRelation
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Div

/-! The sole homogeneous invariant relation. Reduction by the monic quadratic
leaves the unique symmetric normal form proved in the preceding module. -/

noncomputable section

namespace Cubic.SurfaceGeometry.IntegralInvariantPresentation

open InvariantCubicData Cubic.ToricHeights.TernaryCyclicInvariants

theorem relation_degree : Polynomial.IsMonicOfDegree relationPolynomial 2 := by
  have he : relationPolynomial = Polynomial.X ^ 2 +
      Polynomial.C (-(MvPolynomial.X 0 * MvPolynomial.X 1 - 3 * MvPolynomial.X 2)) *
        Polynomial.X + Polynomial.C (MvPolynomial.X 1 ^ 3 +
          MvPolynomial.X 0 ^ 3 * MvPolynomial.X 2 -
          6 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
          9 * MvPolynomial.X 2 ^ 2) := by
    simp [relationPolynomial]
    ring
  rw [he]
  exact Polynomial.isMonicOfDegree_add_add_two _ _

theorem relation_root : relationPolynomial.eval₂ symmetricEval.toRingHom delta = 0 := by
  have h := SurfaceInvariantRelation.«eqn:surfaceInvariantRelation»
  unfold CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim at h
  simp [relationPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_sub, map_add, map_mul, map_pow, map_ofNat, symmetricEval]
  simp only [e, MvPolynomial.esymm_one] at h
  linear_combination h

theorem relations_iff (p : Polynomial SymmetricCoefficients) :
    p.eval₂ symmetricEval.toRingHom delta = 0 ↔ relationPolynomial ∣ p := by
  constructor
  · intro hp
    have hne : relationPolynomial ≠ 1 := by
      intro he
      have h := relation_degree.natDegree_eq
      rw [he, Polynomial.natDegree_one] at h
      contradiction
    have hd := Polynomial.natDegree_modByMonic_lt p relation_degree.monic hne
    rw [relation_degree.natDegree_eq] at hd
    obtain ⟨b,a,he⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one
      (by omega : (p %ₘ relationPolynomial).natDegree ≤ 1)
    have hv := Polynomial.eval₂_modByMonic_eq_self_of_root
      (p := p) relation_degree.monic relation_root
    rw [he, hp] at hv
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe] at hv
    change symmetricEval b * delta + symmetricEval a = 0 at hv
    have hz : normalForm (a,b) = normalForm (0,0) := by
      simp only [normalForm, map_zero, zero_mul, zero_add]
      linear_combination hv
    have hab := IntegralInvariantNormalForm.normalForm_injective hz
    have ha := congrArg Prod.fst hab
    have hb := congrArg Prod.snd hab
    change a = 0 at ha
    change b = 0 at hb
    apply (Polynomial.modByMonic_eq_zero_iff_dvd relation_degree.monic).mp
    simpa [ha,hb] using he
  · rintro ⟨q,rfl⟩
    rw [Polynomial.eval₂_mul, relation_root, zero_mul]

end Cubic.SurfaceGeometry.IntegralInvariantPresentation
