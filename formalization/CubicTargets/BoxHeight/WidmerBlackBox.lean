import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cited black box: [Widmer 2016, Theorem 1.1] for cyclic cubic ground fields

M. Widmer, *Integral points of fixed degree and bounded height*, Int. Math. Res. Not. IMRN
2016, no. 13, 3906–3943, arXiv:1309.1944, Theorem 1.1:

> Let `k` be a number field and `m = [k : ℚ]`. Suppose that either `e = 1` or that
> `n > e + C_{e,m}`, and set `t = t_e(k)`. Then the sums in (1.5) converge, and for `X ≥ 1`
> we have
> `|N(O_k(n; e), X) − Σ_{i=0}^{t} D_i X^{men} (log X^{men})^i| ≤ c₁ X^{men−1} (log⁺ X)^t`
> for some positive constant `c₁ = c₁(n, m, e)` depending only on `n`, `m` and `e`.

Here `N(O_k(n; e), X)` is the number of `α ∈ O_kⁿ` with `[k(α) : k] = e` and absolute
multiplicative Weil height `H(α) ≤ X`; `t_e(k) = e(q_k + 1) − 1`, where `q_k` is the unit
rank; `D_i = Σ_{K ∈ C_e(k), q_K ≥ i} (B_Kⁿ / i!) binom(q_K, i)` with
`B_K = 2^{r_K} (2π)^{s_K} / √|Δ_K|`; and `log⁺ X = max(1, log X)`.

This is the statement specialized, with nothing added, to `n = e = 1` and `k` a cyclic cubic
field (a number field of degree `m = 3` that is Galois over `ℚ`), as authorized:

* For `e = 1`, `C_1(k) = {k}` and `O_k(1; 1) = O_k`, so `t = q_k`, and
  `D_i = (B_k / i!) binom(q_k, i)` for `0 ≤ i ≤ q_k`.
* `X^{men} = X^3`, and `H(α) ≤ X` is written `mulHeight₁ α ≤ X ^ 3`: mathlib's
  `Height.mulHeight₁ x = Π_v max(|x|_v, 1)^{d_v}` is the relative height, equal to `H(x)^m`.
* `c₁` depends only on `n, m, e`, which are fixed here (`n = e = 1`, `m = 3`), so one `c₁`
  serves every cyclic cubic `k` (`∃ c₁, ∀ k`). This uniformity is used by the explicit lower
  bound `thm:lower` of `box_height_research_note.tex`, which sums the error over about
  `H^{1/3}` fields.
* `r_k, s_k, q_k` are mathlib's `nrRealPlaces`, `nrComplexPlaces` and `Units.rank`.

It is a proposition definition: it has no proof and introduces no axiom. Proofs using it
carry it as a visible hypothesis.
-/

noncomputable section

namespace CubicTargets.BoxHeight.WidmerBlackBox

open NumberField NumberField.InfinitePlace

/-- `B_k = 2^{r_k} (2π)^{s_k} / √|Δ_k|`. -/
def B (k : Type*) [Field k] [NumberField k] : ℝ :=
  2 ^ nrRealPlaces k * (2 * Real.pi) ^ nrComplexPlaces k / Real.sqrt |(discr k : ℝ)|

/-- `D_i = (B_k / i!) binom(q_k, i)` (the case `n = e = 1`). -/
def D (k : Type*) [Field k] [NumberField k] (i : ℕ) : ℝ :=
  B k / (i.factorial : ℝ) * ((Units.rank k).choose i : ℝ)

/-- [Widmer 2016, Theorem 1.1] for `n = e = 1` and `k` cyclic cubic. -/
def BlackBox : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (k : Type) [Field k] [NumberField k], Module.finrank ℚ k = 3 → IsGalois ℚ k →
      ∀ X : ℝ, 1 ≤ X →
        |(Nat.card {α : 𝓞 k // Height.mulHeight₁ (α : k) ≤ X ^ 3} : ℝ) -
            ∑ i ∈ Finset.range (Units.rank k + 1), D k i * X ^ 3 * Real.log (X ^ 3) ^ i| ≤
          c₁ * X ^ 2 * max 1 (Real.log X) ^ Units.rank k

end CubicTargets.BoxHeight.WidmerBlackBox
