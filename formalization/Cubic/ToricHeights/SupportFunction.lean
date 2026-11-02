import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Ring

/-!
# The cubic fan's invariant support function

The rays are `v₀ = (-1,-1)`, `v₁ = (1,0)`, `v₂ = (0,1)`.
For divisor parameters `(s₀,σ,σ)`, the support function has values
`(-s₀,-σ,-σ)` on those rays and is linear on each of the three cones.
This is the finite-place height's support function, before any integral cutoff.
-/

noncomputable section

namespace Cubic.ToricHeights

/-- The support function on the whole real cocharacter plane. -/
def supportFunction (s₀ σ : ℂ) (n : ℝ × ℝ) : ℂ :=
  let m := min 0 (min n.1 n.2)
  s₀ * (m : ℂ) - σ * ((n.1 : ℂ) + (n.2 : ℂ) - 2 * (m : ℂ))

theorem supportFunction_continuous (s₀ σ : ℂ) : Continuous (supportFunction s₀ σ) := by
  unfold supportFunction
  fun_prop

theorem supportFunction_swap (s₀ σ : ℂ) (n : ℝ × ℝ) :
    supportFunction s₀ σ n.swap = supportFunction s₀ σ n := by
  simp only [supportFunction, Prod.fst_swap, Prod.snd_swap, min_comm n.2 n.1]
  ring

/-- Scaling the valuation vector by a nonnegative real scales its support value.
In particular, division by the ramification index can be moved outside `φ`. -/
theorem supportFunction_nonneg_smul (s₀ σ : ℂ) (n : ℝ × ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    supportFunction s₀ σ (c * n.1, c * n.2) = c * supportFunction s₀ σ n := by
  have hmin : min 0 (min (c * n.1) (c * n.2)) = c * min 0 (min n.1 n.2) := by
    rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc, mul_zero]
  simp only [supportFunction, hmin, Complex.ofReal_mul]
  ring

/-- Negating divisor parameters negates the support function, on every cone. -/
theorem supportFunction_neg (s₀ σ : ℂ) (n : ℝ × ℝ) :
    supportFunction (-s₀) (-σ) n = -supportFunction s₀ σ n := by
  simp only [supportFunction]
  ring

/-- Moving the divisor parameters by the negative of `a(-2D₀+D₁+D₂)`
adds the linear function paired with `a(a'+b')`, on every cone. -/
theorem supportFunction_principal_shift (s₀ σ a : ℂ) (n : ℝ × ℝ) :
    supportFunction (s₀ + 2 * a) (σ - a) n =
      supportFunction s₀ σ n + a * ((n.1 : ℂ) + n.2) := by
  simp only [supportFunction]
  ring

theorem supportFunction_on_integralCone (s₀ σ : ℂ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    supportFunction s₀ σ (x, y) = -σ * ((x : ℂ) + y) := by
  simp [supportFunction, min_eq_left (le_min hx hy), neg_mul]

theorem supportFunction_on_cone01 (s₀ σ : ℂ) {x y : ℝ}
    (hy : y ≤ 0) (hyx : y ≤ x) :
    supportFunction s₀ σ (x, y) = s₀ * y - σ * ((x : ℂ) - y) := by
  simp only [supportFunction, min_eq_right hyx, min_eq_right hy]
  ring

theorem supportFunction_on_cone02 (s₀ σ : ℂ) {x y : ℝ}
    (hx : x ≤ 0) (hxy : x ≤ y) :
    supportFunction s₀ σ (x, y) = s₀ * x - σ * ((y : ℂ) - x) := by
  rw [← supportFunction_swap]
  exact supportFunction_on_cone01 s₀ σ hx hxy

@[simp]
theorem supportFunction_v0 (s₀ σ : ℂ) : supportFunction s₀ σ (-1, -1) = -s₀ := by
  norm_num [supportFunction]

@[simp]
theorem supportFunction_v1 (s₀ σ : ℂ) : supportFunction s₀ σ (1, 0) = -σ := by
  norm_num [supportFunction]

@[simp]
theorem supportFunction_v2 (s₀ σ : ℂ) : supportFunction s₀ σ (0, 1) = -σ := by
  norm_num [supportFunction]

end Cubic.ToricHeights
