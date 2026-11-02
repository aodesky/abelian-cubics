# On monic abelian cubic polynomials

Lean formalization of the paper by Shubhrajit Bhattacharya and Andrew O’Desky.

[Project website](https://aodesky.github.io/abelian-cubics/) ·
[Blueprint](https://aodesky.github.io/abelian-cubics/blueprint/) ·
[Paper on arXiv](https://arxiv.org/abs/2310.17831)

The formalization follows the authors’ November 2026 revision, including the
count of monic cyclic cubics of arbitrary trace. The arXiv version has the
older title *On monic abelian trace-one cubic polynomials*.

The blueprint contains the current labelled statements, short proof notes,
links to Lean declarations, and a dependency graph extracted from the proofs.
Selected shared supporting lemmas are included to show how the proofs connect.
See [CORRESPONDENCE.md](CORRESPONDENCE.md) for the two alternative analytic
proofs, the rational-point scope of the moduli theorem, and the explicit
literature inputs. The main counting proofs assume Poisson summation and the
Chandrasekharan–Narasimhan critical-line mean-square bound.

## Build and check

Install [Lean via elan](https://github.com/leanprover/elan). The toolchain and
Mathlib dependency are pinned.

```sh
cd formalization
lake exe cache get
python3 scripts/check.py
```

The check builds the project, audits all project declarations for nonstandard
axioms, and checks the registry’s target types and proof files. The paper
check in this public repository compares against the reviewed statement
extracts in `blueprint/paper-statements.tex`; the full working manuscript is
maintained separately.

## Rebuild the blueprint

Install Graphviz and the Python packages in `blueprint/requirements.txt`, then
run from the repository root:

```sh
python3 scripts/blueprint_dependencies.py
python3 scripts/build_blueprint.py
python3 scripts/check_site.py
```

Commit changed Lean sources before rebuilding: links to Lean declarations are
pinned to the source commit. The generated website is committed, and GitHub
Pages checks its manifest and local links before deploying it. Lean changes
also trigger the build and axiom checks in CI.

## Source

`formalization/Cubic/` contains definitions and proofs.
`formalization/CubicTargets/` contains the paper statements.
`formalization/results.json` maps TeX labels to declarations and records
the precise literature inputs.
`blueprint/src/` contains the explanations and generated statements.

The website shares the navigation, colors, and light/dark theme of the
other formalization pages linked from andrewodesky.com. Code adapted from
PrimeNumberTheoremAnd retains its attribution and Apache 2.0 license in
`formalization/third_party/`.
