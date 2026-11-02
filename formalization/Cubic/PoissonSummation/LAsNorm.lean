import CubicTargets.PoissonSummation.LAsNorm
import Cubic.PoissonSummation.AdelicRationalCharacter

/-!
# Proof of `eqn:LAsNorm`

The paper calls this "easy to check". The check is place by place: pairing each place's
contribution `ℓ_w(x_w) log q_w/[E:ℚ]` (summed over the places over `v`) with `N` gives
`-log |N(x_v)|_v` (`QuotientNormLogarithm.infinite_logarithm`,
`AdelicRationalCharacter.local_logarithm_eq_norm`; the minus sign comes from
`|·|_w = q_w^{-ord_w}`). At the primes where `x_p` lies in the maximal compact subgroup the
logarithm vanishes, so `‖N(x_p)‖ = 1`; hence the adelic product has finitely many
nontrivial factors, and summing the local identities gives the claim.
-/

noncomputable section

namespace Cubic.PoissonSummation.LAsNorm

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open QuotientFiniteFourierProduct RationalAdelicEmbedding
open CubicTargets.PoissonSummation.LAsNorm

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem pairing_normCharacter (n : ℝ × ℝ) : pairing normCharacter n = n.1 + n.2 := by
  simp [pairing, normCharacter, CharacterLattice.pullback]

theorem localNorm_ne_zero (p : Nat.Primes) (y : (family p).Carrier) : localNorm p y ≠ 0 :=
  Units.ne_zero _

theorem local_pairing (p : Nat.Primes) (y : (family p).Carrier) :
    pairing normCharacter (FiniteAdelicData.localLogarithm p y) =
      -Real.log ‖localNorm p y‖ := by
  rw [pairing_normCharacter, AdelicRationalCharacter.local_logarithm_eq_norm]
  simp only [localNorm]
  ring

theorem localNorm_eq_one (p : Nat.Primes) (y : (family p).Carrier)
    (hy : y ∈ (family p).maxCompact) : ‖localNorm p y‖ = 1 := by
  have h := local_pairing p y
  rw [FiniteAdelicData.local_logarithm_zero p y hy, pairing_normCharacter] at h
  have hl : Real.log ‖localNorm p y‖ = 0 := by
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h
    linarith
  have hpos : 0 < ‖localNorm p y‖ := norm_pos_iff.mpr (localNorm_ne_zero p y)
  rcases Real.log_eq_zero.mp hl with h0 | h1 | hm
  · exact absurd h0 hpos.ne'
  · exact h1
  · linarith

theorem «eqn:LAsNorm» : Claim := by
  classical
  have key : ∀ x : AdelicData.Points, ∃ S : Finset Nat.Primes,
      ∀ p ∉ S, x.2 p ∈ (family p).maxCompact := by
    intro x
    have hfin : {p | x.2 p ∉ (family p).maxCompact}.Finite := x.2.property
    exact ⟨hfin.toFinset, fun p hp => by
      by_contra hn
      exact hp (hfin.mem_toFinset.mpr hn)⟩
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨S, hS⟩ := key x
    apply S.finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (localNorm_eq_one p _ (hS p hn))
  · obtain ⟨S, hS⟩ := key x
    have hprod : ∏' p : Nat.Primes, ‖localNorm p (x.2 p)‖ = ∏ p ∈ S, ‖localNorm p (x.2 p)‖ :=
      tprod_eq_prod fun p hp => localNorm_eq_one p _ (hS p hp)
    have hinf : infiniteNorm x.1 ≠ 0 := Units.ne_zero _
    rw [adelicNorm, hprod, Real.log_mul (abs_ne_zero.mpr hinf)
      (Finset.prod_ne_zero_iff.mpr fun p _ => norm_ne_zero_iff.mpr (localNorm_ne_zero p _)),
      Real.log_prod (fun p _ => norm_ne_zero_iff.mpr (localNorm_ne_zero p _))]
    change pairing normCharacter (ArchimedeanQuotientLogarithm.logarithm x.1 +
      FiniteAdelicData.logarithm x.2) = _
    rw [FiniteAdelicData.logarithm_eq_sum x.2 S (fun p hp => hS p hp), pairing_normCharacter,
      Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
      QuotientNormLogarithm.infinite_logarithm]
    have hl : ∀ p ∈ S, (FiniteAdelicData.localLogarithm p (x.2 p)).1 +
        (FiniteAdelicData.localLogarithm p (x.2 p)).2 = -Real.log ‖localNorm p (x.2 p)‖ :=
      fun p _ => by rw [← pairing_normCharacter]; exact local_pairing p _
    have hs : ∑ p ∈ S, (FiniteAdelicData.localLogarithm p (x.2 p)).1 +
        ∑ p ∈ S, (FiniteAdelicData.localLogarithm p (x.2 p)).2 =
          ∑ p ∈ S, -Real.log ‖localNorm p (x.2 p)‖ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hl
    simp only [infiniteNorm, Real.norm_eq_abs] at hs ⊢
    rw [Finset.sum_neg_distrib] at hs
    linarith

end Cubic.PoissonSummation.LAsNorm
