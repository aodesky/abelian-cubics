# Correspondence with the paper

This release follows the authors’ revision of *On monic abelian cubic
polynomials* dated 2 November 2026. The arXiv version has an older title and
does not include all the results of this revision. `formalization/results.json`
maps the manuscript’s TeX labels to Lean statements and proof files.
`blueprint/paper-statements.tex` contains the corresponding statement extracts;
it is not the full manuscript.

The geometric calculations use explicit invariant rings, lattices, fans,
divisors, and local coordinates. These are the computational models used by
the proofs. Theorem 5 (`thm:modularInterpretation`) is formalized for rational
points; the functorial statement over general bases is not formalized.

Two proofs use different arguments from the printed paper:

| Result | Paper | Lean |
| --- | --- | --- |
| `lemma:xiMeanValue`, including `eqn:xiMeanBound` | Titchmarsh, §7.8, (7.8.3) | The residue theorem, with a reflected kernel to obtain a bound uniform on the closed strip |
| `eqn:dSummatoryForGeneralTrace`, in the proof of Theorem 2 | Alberts, Theorem 1.1 | Truncated Perron’s formula and contour shifting |

Later results use these estimates. Neither Titchmarsh’s result nor Alberts’s
theorem is an extra hypothesis in Lean.

The main counting proofs assume Poisson summation with the normalized dual
Haar measure, and Chandrasekharan–Narasimhan, Theorem 4, (80), specialized to
the Dedekind zeta function of ℚ(√−3). The Santens comparison in Appendix B and
the alternative ideal count in Remark 1 have their own explicit literature
inputs. Their exact statements and sources are recorded in `cited_black_boxes`
in the registry. These inputs are proposition definitions and hypotheses of
the results that use them, not Lean axioms.

Older results retained in the library are recorded under `historical_results`.
They include the separate Galois-group note (formerly Appendix C), the affine
model material now commented out in the manuscript, and the ellipse lattice
estimate now written inline in Lemma 10. They are not counted as additional
results of the current paper. The older Topacogullari interface is retained,
but is not an assumption of the current main counting theorems.

The dependency graph follows elaborated Lean proofs through their helper
lemmas, stopping at the next registered result. It records formal proof
dependencies, not merely imports. Some paper displays are consequences of a
larger theorem in Lean, so their graph positions need not follow printed order.

The release checks compile the full project, check every project declaration
for nonstandard axioms, check the registered target types and proof files,
and verify the blueprint’s declaration links. These mechanical checks do not
establish semantic equivalence with the manuscript; that correspondence was
reviewed during development.
