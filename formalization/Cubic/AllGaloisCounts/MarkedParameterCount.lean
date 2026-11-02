import Cubic.AllGaloisCounts.MarkedLatticeData

/-! Exact counting by the unique parameters `(a,r,v)`, with both outer
integer ranges obtained from the coefficient and root bounds. -/

noncomputable section

namespace Cubic.AllGaloisCounts.MarkedParameterCount
open Polynomial CountData HeightBox IntegerIntervalCount MarkedFactorization MarkedLatticeData
open Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralMonicCount
open Cubic.Counting.GeneralHeightReduction

theorem parameter_bijOn {H : ℝ} (hH : 0 ≤ H) :
    Set.BijOn toMarked (parameters H) (markedSet H) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, r, v⟩ hp
    refine ⟨⟨⟨a, v - r * (r + a), -r * v, rfl⟩, ?_⟩, marked_root a r v⟩
    exact (marked_height_iff a r v hH).mpr hp
  · rintro ⟨a, r, v⟩ _ ⟨b, s, w⟩ _ he
    have hr := congrArg Prod.snd he
    change r = s at hr
    subst s
    have ha := congrArg (fun p : ℤ[X] × ℤ => p.1.coeff 2) he
    have hv := congrArg (fun p : ℤ[X] × ℤ => p.1.coeff 1) he
    simp only [toMarked, markedPolynomial, monicCubic_coeff_two, monicCubic_coeff_one] at ha hv
    subst b
    have hvw : v = w := by linarith
    subst w
    rfl
  · rintro ⟨f, r⟩ ⟨hf, hr⟩
    obtain ⟨⟨a, v⟩, he, _⟩ := unique_parameters hf.1 hr
    refine ⟨(a, r, v), ?_, ?_⟩
    · exact (marked_height_iff a r v hH).mp (he ▸ hf.2)
    · exact Prod.ext he.symm rfl

theorem parameters_finite {H : ℝ} (hH : 0 ≤ H) : (parameters H).Finite :=
  (parameter_bijOn hH).finite_iff_finite.mpr (markedSet_finite H)

theorem outer_mem {H : ℝ} (hH : 0 ≤ H) {p : ℤ × ℤ × ℤ} (hp : p ∈ parameters H) :
    (p.1, p.2.1) ∈ (T H).product (T (2 * H)) := by
  have hm := (parameter_bijOn hH).mapsTo hp
  have hr := integral_root_bound hm.1 hm.2
  change (p.1, p.2.1) ∈ (T H) ×ˢ (T (2 * H))
  simp only [Finset.mem_product, T, Finset.mem_Icc]
  exact ⟨(int_abs_iff _ _).mp hp.1, (int_abs_iff _ _).mp hr⟩

def fiber (H : ℝ) (a r : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | p ∈ parameters H ∧ (p.1, p.2.1) = (a, r)}

theorem fiber_bijOn {H : ℝ} {a r : ℤ} (ha : |(a : ℝ)| ≤ H) :
    Set.BijOn (fun p : ℤ × ℤ × ℤ => p.2.2) (fiber H a r) (vSet H a r) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, s, v⟩ ⟨hp, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hp.2
  · rintro ⟨b, s, v⟩ ⟨_, hb⟩ ⟨c, t, w⟩ ⟨_, hc⟩ he
    change v = w at he
    simp only [Prod.mk.injEq] at hb hc
    simp only [hb.1, hb.2, hc.1, hc.2, he]
  · intro v hv
    exact ⟨(a, r, v), ⟨⟨ha, hv⟩, rfl⟩, rfl⟩

theorem parameters_card {H : ℝ} (hH : 0 ≤ H) : Nat.card (parameters H) =
    ∑ a ∈ T H, ∑ r ∈ T (2 * H), Nat.card (vSet H a r) := by
  classical
  have hfin := parameters_finite hH
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ × ℤ => (p.1, p.2.1))
      (t := (T H).product (T (2 * H)))
      (fun p hp => outer_mem hH ((Set.Finite.mem_toFinset hfin).mp hp))]
  change (∑ b ∈ (T H) ×ˢ (T (2 * H)),
    (hfin.toFinset.filter (fun p => (p.1, p.2.1) = b)).card) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro r _
  have hf : (hfin.toFinset.filter (fun p => (p.1, p.2.1) = (a, r))).card =
      Nat.card (fiber H a r) := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp [fiber]
  rw [hf]
  exact Nat.card_congr (fiber_bijOn
    (Cubic.Counting.GeneralTraceDecomposition.abs_le_of_mem ha)).equiv

theorem marked_card {H : ℝ} (hH : 0 ≤ H) : markedCount H =
    ∑ a ∈ T H, ∑ r ∈ T (2 * H), Nat.card (vSet H a r) := by
  rw [markedCount, ← Nat.card_congr (parameter_bijOn hH).equiv, parameters_card hH]

end Cubic.AllGaloisCounts.MarkedParameterCount
