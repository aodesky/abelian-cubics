import Cubic.SurfaceGeometry.QuadraticNormCoordinates

noncomputable section

namespace Cubic.SurfaceGeometry.NormTorus

open RationalFormData QuadraticNormCoordinates
open Cubic.QuadraticCorrespondence.CyclotomicField
open scoped TensorProduct

variable (R : Type*) [CommRing R] [Algebra ℚ R]

theorem inverse_formula (x : TorusChart R) :
    quadraticElement (x.val 1) (x.val 2) *
      quadraticElement (x.val 0 * x.val 1) (-(x.val 0 * x.val 2)) = 1 := by
  rw [element_mul]
  calc
    _ = quadraticElement (x.val 0 * (x.val 1 ^ 2 + 3 * x.val 2 ^ 2)) 0 := by
      congr 1 <;> ring
    _ = 1 := by rw [x.property,element_one]

def toUnit (x : TorusChart R) : (E ⊗[ℚ] R)ˣ where
  val := quadraticElement (x.val 1) (x.val 2)
  inv := quadraticElement (x.val 0 * x.val 1) (-(x.val 0 * x.val 2))
  val_inv := inverse_formula R x
  inv_val := by rw [mul_comm]; exact inverse_formula R x

theorem toUnit_injective : Function.Injective (toUnit R) := by
  intro x y h
  have hc : (x.val 1,x.val 2) = (y.val 1,y.val 2) :=
    element_injective (congrArg Units.val h)
  have h1 : x.val 1 = y.val 1 := congrArg Prod.fst hc
  have h2 : x.val 2 = y.val 2 := congrArg Prod.snd hc
  have hx := x.property
  have hy := y.property
  rw [← h1,← h2] at hy
  have h0 : x.val 0 = y.val 0 := by
    linear_combination y.val 0 * hx - x.val 0 * hy
  apply Subtype.ext
  funext i
  fin_cases i <;> assumption

theorem toUnit_surjective : Function.Surjective (toUnit R) := by
  intro u
  obtain ⟨⟨a,b⟩,hab⟩ := element_surjective (u : E ⊗[ℚ] R)
  obtain ⟨⟨c,d⟩,hcd⟩ := element_surjective (u⁻¹ : (E ⊗[ℚ] R)ˣ).val
  dsimp at hab hcd
  have hp : quadraticElement (a*c-3*b*d) (a*d+b*c) = quadraticElement (1 : R) 0 := by
    rw [← element_mul,hab,hcd,element_one]
    exact u.val_inv
  have hcoeff : (a*c-3*b*d,a*d+b*c) = (1,0) := element_injective hp
  have h0 : a*c-3*b*d = 1 := congrArg Prod.fst hcoeff
  have h1 : a*d+b*c = 0 := congrArg Prod.snd hcoeff
  have hN : (c^2+3*d^2)*(a^2+3*b^2) = 1 := by
    rw [mul_comm,← QuadraticNormCoordinates.norm_mul,h0,h1]
    ring
  refine ⟨⟨![c^2+3*d^2,a,b],by simpa using hN⟩,?_⟩
  apply Units.ext
  exact hab

def equivalence : TorusChart R ≃ (E ⊗[ℚ] R)ˣ :=
  Equiv.ofBijective (toUnit R) ⟨toUnit_injective R,toUnit_surjective R⟩

theorem equivalence_value (x : TorusChart R) :
    (equivalence R x : E ⊗[ℚ] R) = quadraticElement (x.val 1) (x.val 2) := rfl

theorem product_closed (x y : TorusChart R) :
    torusProduct x.val y.val 0 *
      ((torusProduct x.val y.val 1)^2+3*(torusProduct x.val y.val 2)^2) = 1 := by
  simp only [torusProduct,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [QuadraticNormCoordinates.norm_mul]
  calc
    _ = (x.val 0 * (x.val 1^2+3*x.val 2^2)) *
        (y.val 0 * (y.val 1^2+3*y.val 2^2)) := by ring
    _ = 1 := by rw [x.property,y.property]; ring

def product (x y : TorusChart R) : TorusChart R :=
  ⟨torusProduct x.val y.val,product_closed R x y⟩

theorem equivalence_mul (x y z : TorusChart R)
    (h : z.val = torusProduct x.val y.val) :
    equivalence R z = equivalence R x * equivalence R y := by
  apply Units.ext
  change quadraticElement (z.val 1) (z.val 2) =
    quadraticElement (x.val 1) (x.val 2) * quadraticElement (y.val 1) (y.val 2)
  rw [h,element_mul]
  rfl

def mapPoint {S : Type*} [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (x : TorusChart R) : TorusChart S :=
  ⟨φ ∘ x.val,by simpa only [Function.comp_apply,map_mul,map_add,map_pow,map_ofNat,map_one]
    using congrArg φ x.property⟩

theorem equivalence_natural {S : Type*} [CommRing S] [Algebra ℚ S]
    (φ : R →ₐ[ℚ] S) (x : TorusChart R) :
    equivalence S (mapPoint R φ x) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) φ).toMonoidHom
        (equivalence R x) := by
  apply Units.ext
  exact (element_map φ (x.val 1) (x.val 2)).symm

end Cubic.SurfaceGeometry.NormTorus
