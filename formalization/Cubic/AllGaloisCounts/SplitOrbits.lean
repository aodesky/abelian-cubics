import Cubic.AllGaloisCounts.MarkedFactorization
import Cubic.Counting.TraceZeroSplitCount

/-! Integral-root triples and the actual trivial-Galois-group count. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SplitOrbits
open Polynomial CountData HeightBox MarkedFactorization
open Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralHeightReduction
open Cubic.Counting.TraceZeroSplitCount (cubicOf roots_cubicOf exists_perm monicCubic_monic)

theorem trivial_iff_splits (f : ℚ[X]) : HasGaloisType .trivial f ↔ f.Splits := by
  constructor
  · rintro ⟨e⟩
    apply Cubic.QuadraticCorrespondence.SmallGaloisGroup.splits_of_card_one
    have h := Nat.card_congr e.toEquiv
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using h
  · intro hs
    letI := Gal.uniqueGalOfSplits f hs
    exact ⟨MulEquiv.ofUnique⟩

theorem integral_roots {a b c : ℤ}
    (hs : ((monicCubic a b c).map (Int.castRingHom ℚ)).Splits) :
    ∃ x y z : ℤ, monicCubic a b c = splitCubic x y z := by
  let Q : _root_.Cubic ℚ := ⟨1, a, b, c⟩
  have hQ : Q.a ≠ 0 := one_ne_zero
  have he : Q.toPoly = (monicCubic a b c).map (Int.castRingHom ℚ) := by
    simp [Q, _root_.Cubic.toPoly, monicCubic]
  have hs' : (Q.toPoly.map (RingHom.id ℚ)).Splits := by rw [Polynomial.map_id, he]; exact hs
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three hQ).mp hs'
  have hint : ∀ r : ℚ, r ∈ ({x, y, z} : Multiset ℚ) → ∃ m : ℤ, (m : ℚ) = r := by
    intro r hr
    rw [← h3, _root_.Cubic.roots, _root_.Cubic.map_toPoly, Polynomial.map_id,
      he, mem_roots ((monicCubic_monic _ _ _).map _).ne_zero, IsRoot.def] at hr
    have hr' : aeval r (monicCubic a b c) = 0 := by
      rw [aeval_def, ← hr, eval_map]; rfl
    exact isInteger_of_is_root_of_monic (monicCubic_monic a b c) hr'
  obtain ⟨p, rfl⟩ := hint x (by simp)
  obtain ⟨q, rfl⟩ := hint y (by simp)
  obtain ⟨r, rfl⟩ := hint z (by simp)
  have ha : a = -(p + q + r) := by
    have h := _root_.Cubic.b_eq_three_roots hQ h3
    simp only [Q, RingHom.id_apply, one_mul] at h
    exact_mod_cast h
  have hb : b = p * q + p * r + q * r := by
    have h := _root_.Cubic.c_eq_three_roots hQ h3
    simp only [Q, RingHom.id_apply, one_mul] at h
    exact_mod_cast h
  have hc : c = -(p * q * r) := by
    have h := _root_.Cubic.d_eq_three_roots hQ h3
    simp only [Q, RingHom.id_apply, one_mul] at h
    exact_mod_cast h
  exact ⟨p, q, r, by rw [ha, hb, hc]; rfl⟩

theorem cubicOf_eq (v : Fin 3 → ℤ) : cubicOf v = splitCubic (v 0) (v 1) (v 2) := by
  rw [cubicOf, Fin.prod_univ_three, splitCubic_factorization]

theorem cubicOf_splits (v : Fin 3 → ℤ) :
    ((cubicOf v).map (Int.castRingHom ℚ)).Splits := by
  rw [cubicOf, Fin.prod_univ_three]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact ((Splits.X_sub_C ((v 0 : ℤ) : ℚ)).mul
    (Splits.X_sub_C ((v 1 : ℤ) : ℚ))).mul (Splits.X_sub_C ((v 2 : ℤ) : ℚ))

theorem cubicOf_root (v : Fin 3 → ℤ) (i : Fin 3) : (cubicOf v).eval (v i) = 0 := by
  simp only [cubicOf, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

def Triples (H : ℝ) : Set (Fin 3 → ℤ) := {v | weightedHeight (cubicOf v) ≤ H}

theorem cubicOf_mem {H : ℝ} (v : Triples H) : cubicOf v.1 ∈ galoisSet .trivial H :=
  ⟨⟨⟨_, _, _, (cubicOf_eq v.1)⟩, v.2⟩, (trivial_iff_splits _).mpr (cubicOf_splits _)⟩

theorem coordinate_bound {H : ℝ} (v : Triples H) (i : Fin 3) :
    |(v.1 i : ℝ)| ≤ 2 * H :=
  integral_root_bound (cubicOf_mem v).1 (cubicOf_root _ i)

theorem triples_finite (H : ℝ) : (Triples H).Finite := by
  refine (Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Icc (-⌊2 * H⌋) ⌊2 * H⌋)).subset ?_
  intro v hv i
  exact (int_abs_iff _ _).mp (coordinate_bound ⟨v, hv⟩ i)

instance (H : ℝ) : MulAction (Equiv.Perm (Fin 3)) (Triples H) where
  smul σ v := ⟨fun i => v.1 (σ⁻¹ i), by
    have h : cubicOf (fun i => v.1 (σ⁻¹ i)) = cubicOf v.1 :=
      Equiv.prod_comp σ⁻¹ (fun i => X - C (v.1 i))
    change weightedHeight _ ≤ H
    rw [h]
    exact v.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_apply {H : ℝ} (σ : Equiv.Perm (Fin 3)) (v : Triples H) (i : Fin 3) :
    (σ • v).1 i = v.1 (σ⁻¹ i) := rfl

theorem cubicOf_smul {H : ℝ} (σ : Equiv.Perm (Fin 3)) (v : Triples H) :
    cubicOf (σ • v).1 = cubicOf v.1 :=
  Equiv.prod_comp σ⁻¹ (fun i => X - C (v.1 i))

def orbitMap (H : ℝ) :
    MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples H) → galoisSet .trivial H :=
  Quotient.lift (fun v => ⟨cubicOf v.1, cubicOf_mem v⟩) (by
    rintro v w ⟨σ, rfl⟩
    exact Subtype.ext (cubicOf_smul σ w))

theorem orbitMap_injective (H : ℝ) : Function.Injective (orbitMap H) := by
  rintro ⟨v⟩ ⟨w⟩ h
  have h' : cubicOf v.1 = cubicOf w.1 := congrArg Subtype.val h
  have hr := congrArg Polynomial.roots h'
  rw [roots_cubicOf, roots_cubicOf, Multiset.coe_eq_coe] at hr
  obtain ⟨σ, hσ⟩ := exists_perm hr
  apply Quotient.sound
  refine ⟨σ, Subtype.ext (funext fun i => ?_)⟩
  rw [smul_apply, hσ]
  simp

theorem orbitMap_surjective (H : ℝ) : Function.Surjective (orbitMap H) := by
  rintro ⟨f, ⟨⟨a, b, c, rfl⟩, hh⟩, hg⟩
  obtain ⟨x, y, z, he⟩ := integral_roots ((trivial_iff_splits _).mp hg)
  have hv : cubicOf ![x, y, z] = monicCubic a b c := by
    rw [cubicOf_eq]
    exact he.symm
  refine ⟨Quotient.mk _ ⟨![x, y, z], ?_⟩, Subtype.ext hv⟩
  change weightedHeight _ ≤ H
  rw [hv]
  exact hh

theorem card_orbits (H : ℝ) :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 3)) (Triples H)) = N .trivial H :=
  Nat.card_congr (Equiv.ofBijective _ ⟨orbitMap_injective H, orbitMap_surjective H⟩)

end Cubic.AllGaloisCounts.SplitOrbits
