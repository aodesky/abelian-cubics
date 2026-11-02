import Cubic.PoissonSummation.LatticeCone
import Cubic.PoissonSummation.FiniteEulerProduct
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp

/-!
# Evaluation of the finite-place lattice sums

The sums run over the explicit lattice cone and its conjugation invariants.
They are not definitions of the Fourier integrals. Identifying those integrals
with these sums, including the height and character, remains a prerequisite.
-/

noncomputable section

namespace Cubic.PoissonSummation.LatticeSeries

open LatticeCone FiniteEulerProduct
open Cubic.OrbitParametrization.CocharacterLattice

/-- The paper's summand `p^(-λ(n₁+n₂))`, in its proved integral degree coordinates. -/
def weight (p : Nat.Primes) (z : ℂ) (n : ConePoint) : ℂ :=
  (p : ℂ) ^ (-z * (degree n : ℂ))

/-- The degree in the summand is the sum of the actual ambient ray coordinates. -/
theorem weight_eq_coordinates (p : Nat.Primes) (z : ℂ) (n : ConePoint) :
    weight p z n = (p : ℂ) ^
      (-z * (((coordinates n.1).1 + (coordinates n.1).2 : ℚ) : ℂ)) := by
  rw [coordinate_sum]
  simp [weight]

theorem weight_eq_pow (p : Nat.Primes) (z : ℂ) (n : ConePoint) :
    weight p z n = ((p : ℂ) ^ (-z)) ^ degree n :=
  Complex.cpow_mul_nat _ _ _

/-- The series supplied by the cardinalities of the split cone's degree slices. -/
theorem hasSum_split_geometric {𝕜 : Type*} [NormedField 𝕜] (x : 𝕜) (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (3 * (k : 𝕜) + 1) * x ^ k) ((1 + 2 * x) / (1 - x) ^ 2) := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have he : x = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hx
  convert ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left (3 : 𝕜)).add
    (hasSum_geometric_of_norm_lt_one hx) using 1
  · funext k
    ring
  · field_simp
    ring

private theorem summable_norm_slices {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun s : Σ k : ℕ, Fin (3 * k + 1) => ‖x ^ s.1‖) := by
  simp_rw [norm_pow]
  apply (summable_sigma_of_nonneg (fun s => pow_nonneg (norm_nonneg x) s.1)).mpr
  constructor
  · intro k
    exact (hasSum_fintype (fun _ : Fin (3 * k + 1) => ‖x‖ ^ k)).summable
  · have h := (hasSum_split_geometric ‖x‖ (by simpa using hx)).summable
    simpa [tsum_fintype] using h

/-- A convergent sum over all split cone points, with the actual multiplicities. -/
theorem hasSum_cone (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ConePoint => x ^ degree n) ((1 + 2 * x) / (1 - x) ^ 2) := by
  have hs : HasSum (fun s : Σ k : ℕ, Fin (3 * k + 1) => x ^ s.1)
      ((1 + 2 * x) / (1 - x) ^ 2) := by
    apply (hasSum_split_geometric x hx).sigma_of_hasSum
    · intro k
      simpa using hasSum_fintype (fun _ : Fin (3 * k + 1) => x ^ k)
    · exact (summable_norm_slices hx).of_norm
  apply sliceEquiv.symm.hasSum_iff.mp
  simpa only [Function.comp_def, degree_sliceEquiv_symm] using hs

/-- A convergent sum over the inert invariant cone, with degree `2k`. -/
theorem hasSum_invariant_cone (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : InvariantConePoint => x ^ degree n.1) (1 - x ^ 2)⁻¹ := by
  have hnorm : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg x]
  apply invariantEquiv.hasSum_iff.mp
  simpa only [Function.comp_def, degree_invariantEquiv, pow_mul] using
    hasSum_geometric_of_norm_lt_one hnorm

/-- The split lattice sum equals the exact local factor in `lemma:finiteFourierProduct`. -/
theorem hasSum_split (p : SplitPrimes) (z : ℂ) (hz : 1 < z.re) :
    HasSum (weight p.1 z) (splitFactor p z) := by
  have hnorm : ‖(p.1 : ℂ) ^ (-z)‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half p.1 hz).trans_lt (by norm_num)
  convert hasSum_cone ((p.1 : ℂ) ^ (-z)) hnorm using 1
  funext n
  exact weight_eq_pow p.1 z n

/-- The inert lattice sum equals the exact local factor in `lemma:finiteFourierProduct`. -/
theorem hasSum_inert (p : InertPrimes) (z : ℂ) (hz : 1 < z.re) :
    HasSum (fun n : InvariantConePoint => weight p.1 z n.1) (inertFactor p z) := by
  have hnorm : ‖(p.1 : ℂ) ^ (-z)‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half p.1 hz).trans_lt (by norm_num)
  have heq : (p.1 : ℂ) ^ (-(2 * z)) = ((p.1 : ℂ) ^ (-z)) ^ 2 := by
    rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]
    norm_num
  simpa only [weight_eq_pow, inertFactor, heq] using
    hasSum_invariant_cone ((p.1 : ℂ) ^ (-z)) hnorm

end Cubic.PoissonSummation.LatticeSeries
