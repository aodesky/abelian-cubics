import Cubic.OrbitParametrization.NormalUnit
import Cubic.OrbitParametrization.TraceOne
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A complex homomorphism and its three distinct cyclic translates for every
actual `C₃`-algebra, including the split algebra. -/

noncomputable section

namespace Cubic.Counting.C3ComplexEmbeddings
open Cubic.OrbitParametrization.C3Algebra

def orbit (K : C3Alg) (τ : K.carrier →ₐ[ℚ] ℂ) (i : Fin 3) : K.carrier →ₐ[ℚ] ℂ :=
  τ.comp (K.act (Multiplicative.ofAdd (i : ZMod 3))).toAlgHom

theorem exists_hom (K : C3Alg) :
    ∃ τ : K.carrier →ₐ[ℚ] ℂ, Function.Injective (orbit K τ) := by
  rcases K.model with ⟨hK, _, hfaithful⟩ | ⟨e, he⟩
  · letI : Field K.carrier := hK.toField
    let τ : K.carrier →ₐ[ℚ] ℂ := IsAlgClosed.lift
    refine ⟨τ, fun i j hij => ?_⟩
    have hact : K.act (Multiplicative.ofAdd (i : ZMod 3)) =
        K.act (Multiplicative.ofAdd (j : ZMod 3)) := by
      ext x
      exact τ.injective (DFunLike.congr_fun hij x)
    exact Multiplicative.ofAdd.injective (hfaithful hact)
  · let τ : K.carrier →ₐ[ℚ] ℂ := (Algebra.ofId ℚ ℂ).comp
      ((Pi.evalAlgHom ℚ (fun _ : ZMod 3 => ℚ) 0).comp e.toAlgHom)
    have hv : ∀ (i : Fin 3) (x : K.carrier), orbit K τ i x = (e x i : ℂ) := by
      intro i x
      change ((e (K.act (Multiplicative.ofAdd (i : ZMod 3)) x) 0 : ℚ) : ℂ) = _
      rw [he]
      simp
    refine ⟨τ, fun i j hij => ?_⟩
    by_contra hne
    have h := DFunLike.congr_fun hij (e.symm (Pi.single (i : ZMod 3) 1))
    rw [hv, hv, e.apply_symm_apply] at h
    simp [Ne.symm hne] at h

theorem orbit_matrix (K : C3Alg) (τ : K.carrier →ₐ[ℚ] ℂ) (x : K.carrier) :
    (fun i j : Fin 3 => orbit K τ i (K.act (Multiplicative.ofAdd (j : ZMod 3)) x)) =
      Cubic.OrbitParametrization.conjugates (τ x) (τ (K.act σ x))
        (τ (K.act (σ ^ 2) x)) := by
  funext i j
  simp only [orbit, AlgHom.comp_apply, AlgEquiv.coe_algHom,
    ← AlgEquiv.mul_apply, ← map_mul]
  fin_cases i <;> fin_cases j <;>
    first | rfl | (change τ (K.act 1 x) = τ x; rw [map_one]; rfl)

end Cubic.Counting.C3ComplexEmbeddings
