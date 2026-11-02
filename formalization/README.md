# Lean sources

Run `lake exe cache get` and `python3 scripts/check.py` here.
The pinned toolchain is Lean 4.28.0, with Mathlib v4.28.0.

`Cubic.lean` and `CubicTargets.lean` import every project module.
`Audit.lean` checks the transitive axioms of every project declaration.
The registry keeps current-paper results separate from retained older results.

See the repository’s [correspondence record](../CORRESPONDENCE.md) for scope
and proof differences. The public statement extracts are in
[`blueprint/paper-statements.tex`](../blueprint/paper-statements.tex).
