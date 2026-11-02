import Cubic.SantensComparison.PicardLattices
import Cubic.QuadraticCorrespondence.CyclotomicConjugation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Instances.Int
import Mathlib.Data.Set.Finite.Lemmas

/-! Continuous first cocycles of the actual open Picard permutation lattice.
The elementary degree-one permutation-module argument below also applies to
the absolute Galois group: continuity and compactness give finite coordinate
ranges. Thus this is not merely the cohomology of the quadratic quotient. -/

noncomputable section
open scoped Classical

namespace Cubic.SantensComparison.PermutationCohomology

open Cubic.QuadraticCorrespondence.CyclotomicField FanData PicardLattices

/-- The degree-one permutation-module vanishing, with continuity retained.
Taking the maximum of each finite coordinate range produces the coboundary. -/
theorem continuous_permutation_cocycle {G I : Type*} [Group G]
    [TopologicalSpace G] [CompactSpace G] (ρ : G →* Equiv.Perm I)
    (c : G → I → ℤ) (hc : Continuous c)
    (hadd : ∀ g h i, c (g*h) i = c g i + c h (ρ g⁻¹ i)) :
    ∃ b : I → ℤ, ∀ g i, c g i = b (ρ g⁻¹ i) - b i := by
  have hm : ∀ i, ∃ g : G, ∀ h, c h i ≤ c g i := by
    intro i
    have hf := (isCompact_range ((continuous_apply i).comp hc)).finite_of_discrete
    obtain ⟨v,⟨g,rfl⟩,hv⟩ :=
      Set.exists_max_image (Set.range (fun g => c g i)) id hf ⟨c 1 i,1,rfl⟩
    exact ⟨g,fun h => hv _ ⟨h,rfl⟩⟩
  choose k hk using hm
  refine ⟨fun i => -c (k i) i, ?_⟩
  intro g i
  have h₁ := hk i (g * k (ρ g⁻¹ i))
  rw [hadd] at h₁
  have h₂ := hk (ρ g⁻¹ i) (g⁻¹ * k i)
  have h₃ := hadd g (g⁻¹ * k i) i
  simp only [mul_inv_cancel_left] at h₃
  dsimp
  omega

abbrev QuadraticGroup := E ≃ₐ[ℚ] E
abbrev AbsoluteGroup := AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E

local instance : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E

def restriction : AbsoluteGroup →* QuadraticGroup := AlgEquiv.restrictNormalHom E

/-- Left permutation action on the two actual embeddings of E. -/
def embeddingAction : AbsoluteGroup →* Equiv.Perm QuadraticGroup where
  toFun g := Equiv.mulLeft (restriction g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

def pairFunctionEquiv : (ℤ × ℤ) ≃ₗ[ℤ] (QuadraticGroup → ℤ) where
  toFun m σ := if σ=1 then m.1 else m.2
  invFun f := (f 1,f conjugation)
  left_inv m := by simp [show conjugation ≠ (1 : QuadraticGroup) from conjugation_ne_identity]
  right_inv f := by
    ext σ
    rcases automorphism_eq_identity_or_conjugation σ with rfl | rfl
    · simp [show (AlgEquiv.refl : QuadraticGroup)=1 from rfl]
    · simp [show conjugation ≠ (1 : QuadraticGroup) from conjugation_ne_identity]
  map_add' m n := by ext σ; by_cases h : σ=1 <;> simp [h]
  map_smul' r m := by ext σ; by_cases h : σ=1 <;> simp [h]

def picardFunctionEquiv : OpenPicard ≃ₗ[ℤ] (QuadraticGroup → ℤ) :=
  openPicardEquiv.trans pairFunctionEquiv

def action (g : AbsoluteGroup) (m : OpenPicard) : OpenPicard :=
  picardFunctionEquiv.symm (fun σ => picardFunctionEquiv m (embeddingAction g⁻¹ σ))

theorem action_add (g : AbsoluteGroup) (m n : OpenPicard) :
    action g (m+n) = action g m + action g n := by
  apply picardFunctionEquiv.injective
  ext σ
  simp [action]

theorem action_neg (g : AbsoluteGroup) (m : OpenPicard) : action g (-m) = -action g m := by
  apply picardFunctionEquiv.injective
  ext σ
  simp [action]

@[simp] theorem action_zero (g : AbsoluteGroup) : action g 0=0 := by
  apply picardFunctionEquiv.injective
  ext σ
  simp [action]

theorem action_one (m : OpenPicard) : action 1 m=m := by
  simp [action]

theorem action_mul (g h : AbsoluteGroup) (m : OpenPicard) :
    action (g*h) m = action g (action h m) := by
  apply picardFunctionEquiv.injective
  ext σ
  simp [action]

/-- The permutation coordinates are those induced from the original ray
divisors, as certified by `open_picard_conjugation`. -/
theorem action_on_divisors (g : AbsoluteGroup) (d : Fin 4 → ℤ)
    (hg : restriction g = conjugation) :
    action g (Submodule.Quotient.mk d) =
      Submodule.Quotient.mk (conjugateOpenDivisor d) := by
  have hc : conjugation*conjugation=(1 : QuadraticGroup) := by
    ext x
    exact conjugation_involutive x
  have hci : conjugation⁻¹=conjugation := inv_eq_of_mul_eq_one_left hc
  apply picardFunctionEquiv.injective
  ext σ
  simp only [action, LinearEquiv.apply_symm_apply]
  change pairFunctionEquiv (openPicardEquiv (Submodule.Quotient.mk d))
    (restriction g⁻¹*σ) = _
  simp only [map_inv, hg, hci, picardFunctionEquiv, LinearEquiv.trans_apply,
    open_picard_conjugation]
  rcases automorphism_eq_identity_or_conjugation σ with rfl | rfl
  · simp [pairFunctionEquiv, show (AlgEquiv.refl : QuadraticGroup)=1 from rfl,
      show conjugation ≠ (1 : QuadraticGroup) from conjugation_ne_identity]
  · simp [pairFunctionEquiv, hc,
      show conjugation ≠ (1 : QuadraticGroup) from conjugation_ne_identity]

/-- The cocycle group, with the standard discrete topology on the Picard
lattice expressed in its proved integral basis. -/
def cocycles : AddSubgroup (AbsoluteGroup → OpenPicard) where
  carrier := {c | Continuous (fun g => picardFunctionEquiv (c g)) ∧
    ∀ g h, c (g*h)=c g+action g (c h)}
  zero_mem' := by
    constructor
    · simpa using (continuous_const : Continuous (fun _ : AbsoluteGroup => (0 : QuadraticGroup → ℤ)))
    · intro g h; simp
  add_mem' := by
    rintro c d ⟨hc,he⟩ ⟨hd,hf⟩
    constructor
    · simpa using hc.add hd
    · intro g h
      simp only [Pi.add_apply, he, hf, action_add]
      abel
  neg_mem' := by
    rintro c ⟨hc,he⟩
    constructor
    · simpa using hc.neg
    · intro g h
      simp only [Pi.neg_apply, he, neg_add, action_neg]

def coboundaries : AddSubgroup cocycles where
  carrier := {c | ∃ b : OpenPicard, ∀ g, c.val g=action g b-b}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro c d ⟨b,hb⟩ ⟨e,he⟩
    refine ⟨b+e, fun g => ?_⟩
    change c.val g+d.val g=_
    rw [hb,he,action_add]
    abel
  neg_mem' := by
    rintro c ⟨b,hb⟩
    refine ⟨-b,fun g => ?_⟩
    change -c.val g=_
    rw [hb,action_neg]
    abel

abbrev H1 := cocycles ⧸ coboundaries

theorem every_cocycle_is_coboundary (c : cocycles) : c ∈ coboundaries := by
  obtain ⟨b,hb⟩ := continuous_permutation_cocycle embeddingAction
    (fun g => picardFunctionEquiv (c.val g)) c.property.1 (by
      intro g h i
      dsimp only
      rw [c.property.2, map_add]
      simp [action])
  refine ⟨picardFunctionEquiv.symm b,fun g => ?_⟩
  apply picardFunctionEquiv.injective
  ext σ
  simpa [action] using hb g σ

theorem h1_zero : ∀ x : H1, x=0 := by
  intro x
  induction x using Quotient.inductionOn with
  | h c =>
    exact (QuotientAddGroup.eq_zero_iff c).mpr (every_cocycle_is_coboundary c)

end Cubic.SantensComparison.PermutationCohomology
