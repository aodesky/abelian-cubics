# Correspondence with the paper

This release follows the authors’ revision of *On monic abelian cubic
polynomials* dated 5 November 2026. The arXiv version has an older title and
does not include all the results of this revision. `formalization/results.json`
maps the manuscript’s TeX labels to Lean statements and proof files.
`blueprint/paper-statements.tex` contains the corresponding statement extracts;
it is not the full manuscript.

The geometric calculations use explicit invariant rings, lattices, fans,
divisors, and local coordinates. These are the computational models used by
the proofs. Theorem 5 (`thm:modularInterpretation`) is formalized for rational
points; the functorial statement over general bases is not formalized.

Three proofs use different arguments from the printed paper:

| Result | Paper | Lean |
| --- | --- | --- |
| `lemma:xiMeanValue`, including `eqn:xiMeanBound` | Titchmarsh, §7.8, (7.8.3) | The residue theorem, with a reflected kernel to obtain a bound uniform on the closed strip |
| `eqn:dSummatoryForGeneralTrace`, in the proof of Theorem 2 | Alberts, Theorem 1.1 | Truncated Perron’s formula and contour shifting |
| `thm:exactFormula`, the step d_n = a_E(n³) | Count of ideals of prime-power norm | Comparison of Dirichlet coefficients in ζ_E(s) = ζ(s)L(s, χ), with χ the nontrivial character mod 3 |

Later results use the two estimates. Neither Titchmarsh’s result nor Alberts’s
theorem is an extra hypothesis in Lean.

The main counting proofs assume Poisson summation with the normalized dual
Haar measure, and Chandrasekharan–Narasimhan, Theorem 4, (80), specialized to
the Dedekind zeta function of ℚ(√−3). The Santens comparison in Appendix B and
the alternative ideal count in Remark 1 have their own explicit literature
inputs. Their exact statements and sources are recorded in `cited_black_boxes`
in the registry. The Santens input is stated for heights from Santens’s own
metrics, whose local norms at each prime lie in p^ℤ ∪ {0}. As in the paper,
Lean applies it to the height with the trivial metric at every prime and
proves that this height gives the same count and constant as H(·,1). These
inputs are proposition definitions and hypotheses of the results that use
them, not Lean axioms.

Older results retained in the library are recorded under `historical_results`.
They include the separate Galois-group note (formerly Appendix C), the affine
model material now commented out in the manuscript, and the ellipse lattice
estimate now written inline in Lemma 10. They are not counted as additional
results of the current paper. The older Topacogullari interface is retained,
but is not an assumption of the current main counting theorems.

The dependency graph includes the paper's results, literature inputs, and
19 selected supporting lemmas shared by several proofs. It follows elaborated
Lean declarations through other helpers, stopping at the next displayed node.
Every edge records a formal dependency; `blueprint/dependency-evidence.json`
retains a declaration path for each one. Some paper displays are consequences
of a larger theorem in Lean, so their graph positions need not follow printed
order. Two results that share a helper have arrows from that helper, without
implying that either result is proved using the other.

The release checks compile the full project, check every project declaration
for nonstandard axioms, check the registered target types and proof files,
and verify the blueprint’s declaration links. These mechanical checks do not
establish semantic equivalence with the manuscript; that correspondence was
reviewed during development.
