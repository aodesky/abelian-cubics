import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Cubic.PoissonSummation.FiniteEulerProduct

/-!
# The quadratic Dirichlet character used in the continuation argument

This is mathlib's quadratic character of `𝔽₃`, with its integer values mapped
to `ℂ`. The residue classes, nontriviality and entire L-function are proved,
rather than postulated as data for the Euler-factor comparison.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticDirichletCharacter

def character : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem character_zero : character 0 = 0 := by simp [character]

@[simp] theorem character_one : character 1 = 1 := by simp [character]

@[simp] theorem character_two : character 2 = -1 := by
  have h : quadraticChar (ZMod 3) 2 = -1 := by
    rw [quadraticChar_eq_pow_of_char_ne_two (by norm_num [ZMod.ringChar_zmod_n])
      (by decide : (2 : ZMod 3) ≠ 0)]
    norm_num
    decide
  simp [character, h]

theorem character_of_mod (n : ℕ) : character n = character (n % 3 : ℕ) := by
  rw [ZMod.natCast_mod]

theorem character_split (p : FiniteEulerProduct.SplitPrimes) : character (p.1 : ℕ) = 1 := by
  rw [character_of_mod, p.2]
  exact character_one

theorem character_inert (q : FiniteEulerProduct.InertPrimes) : character (q.1 : ℕ) = -1 := by
  rw [character_of_mod, q.2]
  exact character_two

@[simp] theorem character_three : character (3 : ℕ) = 0 := by
  rw [character_of_mod]
  exact character_zero

theorem character_ne_one : character ≠ 1 := by
  intro h
  have he := congrArg (fun χ : DirichletCharacter ℂ 3 => χ (2 : ZMod 3)) h
  dsimp only at he
  rw [character_two] at he
  have hu : IsUnit (2 : ZMod 3) := isUnit_iff_ne_zero.mpr (by decide)
  change (-1 : ℂ) = (1 : MulChar (ZMod 3) ℂ) (2 : ZMod 3) at he
  rw [MulChar.one_apply hu] at he
  norm_num at he

theorem differentiable_LFunction : Differentiable ℂ (DirichletCharacter.LFunction character) :=
  DirichletCharacter.differentiable_LFunction character_ne_one

end Cubic.PoissonSummation.QuadraticDirichletCharacter
