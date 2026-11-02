import Cubic.SurfaceGeometry.ProjectiveChartData
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace Cubic.SurfaceGeometry.ProjectiveCharts

open MvPolynomial ProjectiveChartData VeroneseData
open Cubic.ToricHeights.TernaryCyclicInvariants

local instance invariantCommRing : CommRing invariants := inferInstance
local instance invariantDomain : IsDomain invariants := inferInstance
local instance fractionField : Field InvariantFractionField := inferInstance

theorem homogeneous_thirdVeronese {p : invariants} {n : ℕ}
    (hp : p.val.IsHomogeneous (3 * n)) : p.val ∈ thirdVeronese := by
  refine ⟨p.property, ?_⟩
  intro a ha
  have he := congrArg (fun m : ℕ => (m : ZMod 3)) (hp ha)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at he
  have h3 : (3 : ZMod 3) = 0 := by decide
  simpa [VeroneseGrading.ordinaryWeight, Finsupp.weight_apply, Finsupp.sum, h3] using he

theorem veronese_chart (f : invariants) (d : ℕ) (hf : f.val.IsHomogeneous d)
    (hf0 : f ≠ 0) : Chart f d = VeroneseChart f d := by
  ext x
  constructor
  · rintro ⟨n,p,hp,rfl⟩
    have hq : (p * f ^ (2 * n)).val.IsHomogeneous (3 * (d * n)) := by
      have h := hp.mul (hf.pow (2 * n))
      convert h using 1 <;> ring
    refine ⟨n, ⟨(p * f ^ (2 * n)).val, homogeneous_thirdVeronese hq⟩, hq, ?_⟩
    change fraction (p * f ^ (2 * n)) (f ^ 3) n = fraction p f n
    have hfn : algebraMap invariants InvariantFractionField f ≠ 0 := by
      intro h
      exact hf0 ((IsFractionRing.injective invariants InvariantFractionField)
        (h.trans (map_zero _).symm))
    simp only [fraction, map_mul, map_pow]
    field_simp [hfn]
    ring
  · rintro ⟨n,p,hp,rfl⟩
    refine ⟨3 * n, ⟨p.val,p.property.1⟩, ?_, ?_⟩
    · convert hp using 1 <;> ring
    · simp only [fraction, map_pow, pow_mul]

/-- The chart subalgebra, with the ring operations inherited from the same
fraction field on both sides of the Veronese comparison. -/
def chartAlgebra (f : invariants) (d : ℕ) (hf : f.val.IsHomogeneous d)
    (hf0 : f ≠ 0) : Subalgebra ℤ InvariantFractionField where
  carrier := Chart f d
  zero_mem' := ⟨0, 0, isHomogeneous_zero (Fin 3) ℤ _, by simp [fraction]⟩
  one_mem' := ⟨0, 1, by simpa only [mul_zero] using isHomogeneous_one (Fin 3) ℤ,
    by simp [fraction]⟩
  add_mem' := by
    rintro _ _ ⟨n,p,hp,rfl⟩ ⟨m,q,hq,rfl⟩
    refine ⟨n + m, p * f ^ m + q * f ^ n, ?_, ?_⟩
    · have h₁ := hp.mul (hf.pow m)
      have h₂ := hq.mul (hf.pow n)
      have hd : d * m + d * n = d * n + d * m := by omega
      simpa only [mul_add, Subalgebra.coe_add, Subalgebra.coe_mul,
        Subalgebra.coe_pow] using h₁.add (hd ▸ h₂)
    · have hfn : algebraMap invariants InvariantFractionField f ≠ 0 := by
        intro h
        exact hf0 ((IsFractionRing.injective invariants InvariantFractionField)
          (h.trans (map_zero _).symm))
      dsimp only [fraction]
      rw [(algebraMap invariants InvariantFractionField).map_add,
        (algebraMap invariants InvariantFractionField).map_mul,
        (algebraMap invariants InvariantFractionField).map_mul,
        map_pow, map_pow, pow_add]
      field_simp [hfn]
  mul_mem' := by
    rintro _ _ ⟨n,p,hp,rfl⟩ ⟨m,q,hq,rfl⟩
    refine ⟨n + m, p * q, ?_, ?_⟩
    · simpa only [mul_add] using hp.mul hq
    · simp only [fraction, map_mul, pow_add, mul_div_mul_comm]
  algebraMap_mem' := by
    intro r
    refine ⟨0, algebraMap ℤ invariants r, ?_, ?_⟩
    · simpa using isHomogeneous_C (Fin 3) r
    · simp [fraction]

theorem chart_flat (f : invariants) (d : ℕ) (hf : f.val.IsHomogeneous d)
    (hf0 : f ≠ 0) : Module.Flat ℤ (chartAlgebra f d hf hf0) := by
  letI : CharZero InvariantFractionField := IsFractionRing.charZero invariants
  letI : CharZero (chartAlgebra f d hf hf0) := inferInstance
  letI : IsAddTorsionFree (chartAlgebra f d hf hf0) := IsAddTorsionFree.of_isDomain_charZero
  letI : Module.IsTorsionFree ℤ (chartAlgebra f d hf hf0) := inferInstance
  infer_instance

end Cubic.SurfaceGeometry.ProjectiveCharts
