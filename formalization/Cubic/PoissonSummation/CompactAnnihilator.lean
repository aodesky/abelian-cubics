import Mathlib.Topology.Algebra.PontryaginDual

/-!
# The annihilator of a compact subgroup is open

A circle-valued homomorphism whose values all have positive real part is
trivial: its arguments add without crossing the branch cut, so a nonzero
argument would give unbounded arguments of powers. Compact-open neighborhoods
then show that triviality on a compact subgroup is an open condition.
This is needed to restrict the full automorphic Haar measure to the level
annihilator; it does not choose or normalize that measure.
-/

noncomputable section

namespace Cubic.PoissonSummation.CompactAnnihilator

open Set

theorem circleHom_eq_one_of_re_pos {G : Type*} [Group G] (χ : G →* Circle)
    (hχ : ∀ g, 0 < (χ g : ℂ).re) : χ = 1 := by
  have ha (g : G) : |Complex.arg (χ g)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hχ g))
  have hadd (g h : G) : Complex.arg (χ (g * h)) = Complex.arg (χ g) + Complex.arg (χ h) := by
    rw [map_mul, Circle.coe_mul]
    apply Complex.arg_mul (χ g).coe_ne_zero (χ h).coe_ne_zero
    have hg := abs_lt.mp (ha g)
    have hh := abs_lt.mp (ha h)
    exact ⟨by linarith, by linarith⟩
  apply MonoidHom.ext
  intro g
  have hp (n : ℕ) : Complex.arg (χ (g ^ n)) = n * Complex.arg (χ g) := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, hadd, ih, Nat.cast_add, Nat.cast_one]; ring
  have hz : Complex.arg (χ g) = 0 := by
    by_contra hn
    obtain ⟨n, hn'⟩ := exists_lt_nsmul (abs_pos.mpr hn) (Real.pi / 2)
    rw [nsmul_eq_mul] at hn'
    have hb := ha (g ^ n)
    rw [hp, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hb
    exact (not_lt_of_ge hn'.le) hb
  change χ g = 1
  rw [← Circle.exp_arg (χ g), hz, Circle.exp_zero]

/-- The annihilator carries the topology inherited from the actual Pontryagin dual. -/
theorem isOpen_setOf_trivial_on_compact {G : Type*} [Group G] [TopologicalSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    IsOpen {χ : PontryaginDual G | K ≤ χ.toMonoidHom.ker} := by
  let U : Set Circle := {z | 0 < (z : ℂ).re}
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp continuous_subtype_val)
  have ho : IsOpen {χ : PontryaginDual G | MapsTo χ K U} :=
    (ContinuousMap.isOpen_setOf_mapsTo hK hU).preimage
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
  convert ho using 1
  ext χ
  constructor
  · intro h g hg
    change 0 < (χ g : ℂ).re
    rw [show χ g = 1 from h hg]
    norm_num
  · intro h
    have he := circleHom_eq_one_of_re_pos (χ.toMonoidHom.comp K.subtype)
      (fun g => h g.property)
    intro g hg
    exact DFunLike.congr_fun he (⟨g, hg⟩ : K)

end Cubic.PoissonSummation.CompactAnnihilator
