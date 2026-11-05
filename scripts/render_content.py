#!/usr/bin/env python3
"""Generate blueprint statements from the reviewed registry, with edited proof notes."""

import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'blueprint/src'


def safe_label(label):
    return label.replace('(', '-').replace(')', '')


def clean(text):
    # plasTeX misparses nested dollar math inside \text in an outer math span.
    # This equivalent spelling keeps the split-algebra example in one node.
    text = text.replace(r'\text{$\QQ$-alg}', r'\QQ\text{-alg}')
    # Correct the duplicated font command in the paper's torus notation.
    text = text.replace(r'\mathcal \GG_m', r'\GG_m')
    text = re.sub(r'\\label\{[^}]*\}', '', text)
    # Number statements once, in the blueprint wrapper.
    text = re.sub(r'\\(begin|end)\{(equation|align|multline|gather)\*?\}',
                  lambda m: '\\' + m[1] + '{' + m[2] + '*}', text)
    text = re.sub(r'\\(eqref|ref)\{([^}]*)\}',
                  lambda m: '\\' + m[1] + '{' + safe_label(m[2]) + '}', text)
    return text


def main():
    data = json.loads((ROOT / 'formalization/results.json').read_text())
    graph = json.loads((ROOT / 'blueprint/dependencies.json').read_text())
    order = json.loads((ROOT / 'blueprint/order.json').read_text())
    notes = json.loads((SRC / 'notes.json').read_text())
    contexts = json.loads((SRC / 'contexts.json').read_text())
    helpers = json.loads((SRC / 'helpers.json').read_text())
    named = {'theorem', 'proposition', 'lemma', 'corollary', 'example', 'rem', 'remark'}
    text = [r'\input{introduction}']
    chapter = None
    for item in order:
        label = item['label']
        entry = data['results'][label]
        if item['chapter'] != chapter:
            chapter = item['chapter']
            text.append(r'\chapter{' + item['chapter_title'] + '}')
            if chapter == 'quadratic':
                text.append(r'\label{sec:quadraticParametrization}')
            text.append(contexts.get(chapter, ''))
        kind = entry['kind']
        env = ('remarknode' if kind in {'rem', 'remark'} else kind) if kind in named else 'equationnode'
        statement = entry['statement']
        if kind in named:
            begin = re.match(r'\\begin\{[^}]*\}', statement)
            body = statement[begin.end():]
            # Optional theorem headings can contain citations with nested brackets.
            if body.startswith('['):
                level = 0
                for i, c in enumerate(body):
                    if c == '[': level += 1
                    if c == ']':
                        level -= 1
                        if level == 0:
                            body = body[i + 1:]
                            break
            body = re.sub(r'\\end\{[^}]*\}\s*$', '', body)
        else:
            body = statement
        if label == 'thm:modularInterpretation':
            body = (r'There is a bijection between rational points of $T$ and equivalence '
                    r'classes of $C_3$-algebras $K/\QQ$ equipped with a trace-one normal '
                    r'element $x\in K$.')
        title = notes.get(label, {}).get('title', '')
        opening = r'\begin{' + env + '}' + ('[' + title + ']' if title else '')
        declarations = [entry['target']['declaration']]
        if entry['target'].get('proof'):
            declarations.append(entry['target']['proof'])
        text += [opening, r'\label{' + safe_label(label) + '}',
                 r'\lean{' + ', '.join(declarations) + '}', r'\leanok',
                 notes.get(label, {}).get('context', ''), clean(body),
                 r'\end{' + env + '}']
        if entry['status'] == 'proved':
            text += [r'\begin{proof}[Proof in Lean]', r'\leanok']
            if graph[label]:
                text.append(r'\uses{' + ', '.join(safe_label(k) for k in graph[label]) + '}')
            if label in notes and notes[label].get('proof'):
                text.append(notes[label]['proof'])
            else:
                text.append('The linked Lean proof establishes this statement.')
            assumptions = entry.get('target', {}).get('black_box_assumptions', [])
            if assumptions:
                names = {
                    'eqn:poissonae': 'Poisson summation',
                    'cite:chandrasekharanNarasimhan1963-thm4':
                        'the Chandrasekharan--Narasimhan estimate',
                    'cite:santens2023integral-toric-counting': 'Santens\\textquotesingle s theorem',
                    'cite:kuehleitnerNowak2004-cor2': r'the K\"uhleitner--Nowak estimate',
                }
                text.append('The proof assumes ' +
                            ' and '.join(names[k].replace(r'\textquotesingle s', "'s") +
                                         ' (' + ('Equation' if k.startswith('eqn:') else 'Cited theorem') +
                                         r'~\ref{' + safe_label(k) + '})'
                                         for k in assumptions) + '.')
            text.append(r'\end{proof}')
        else:
            text.append('This is an explicit hypothesis in the formalization.')
    text.append(r'\chapter{Shared supporting lemmas}')
    text.append('These lemmas occur inside several of the Lean proofs. Showing them '
                'as separate nodes makes their shared use visible in the dependency graph. '
                'Their numbering is separate from the statements of the paper.')
    for label, entry in helpers.items():
        text += [r'\begin{supportinglemma}[' + entry['title'] + ']',
                 r'\label{' + label + '}', r'\lean{' + entry['declaration'] + '}',
                 r'\leanok', clean(entry['statement']), r'\end{supportinglemma}',
                 r'\begin{proof}[Proof in Lean]', r'\leanok']
        if graph[label]:
            text.append(r'\uses{' + ', '.join(safe_label(k) for k in graph[label]) + '}')
        text += [entry['proof'], r'\end{proof}']
    text.append(r'\chapter{Literature inputs}')
    text.append('The following inputs are stated in Lean and assumed by the results '
                'that use them. Poisson summation is recorded with the Fourier analysis above.')
    cited_notes = {
        'cite:chandrasekharanNarasimhan1963-thm4': (
            'Chandrasekharan--Narasimhan',
            r'For $E=\QQ(\sqrt{-3})$ and $\xi=\zeta_E$, '
            r'\[\frac1T\int_1^T|\xi(1/2+it)|^2\,dt=O((\log T)^2)\qquad(T\to\infty).\]'
            r'This is \cite[Theorem~4, (80)]{chandrasekharanNarasimhan1963}, '
            r'with $[E:\QQ]=2$ and $\sigma=1/2$.'),
        'cite:santens2023integral-toric-counting': (
            'Santens',
            r'The integral-point counting theorem \cite[Theorem~8.7]{santens2023integral}, '
            r'with its measure normalizations and auxiliary results, is used in the '
            r'rank-two permutation-Picard setting. The Lean input is a general '
            r'computational corollary for smooth complete Galois fans, integral '
            r"subalgebras, and heights from Santens's metrics, whose local norms at "
            r'each prime lie in $p^{\ZZ}\cup\{0\}$. Its hypotheses include the '
            r'geometric positivity conditions and the conditions on integral points; '
            r'its constant is the dual-cone volume times the normalized local integrals. '
            r'Proposition~\ref{prop:santensConstant} verifies those hypotheses and evaluates the constant for this surface. '
            r'The linked Lean proposition gives the full quantified input.'),
        'cite:kuehleitnerNowak2004-cor2': (
            r'K\"uhleitner--Nowak',
            r'For a fixed quadratic field $K$, let $a_K(m)$ be the number of integral '
            r'ideals of norm $m$, and let $b_K(n)=a_K(n^3)$ be the number of integral '
            r'ideals of norm $n^3$. If $F$ is analytic at $1$ and agrees with '
            r'$(s-1)^2\sum_{n\geq1}b_K(n)n^{-s}$ to its right, then '
            r'\[\sum_{n\leq X}b_K(n)=F(1)X\log X+(F^\prime(1)-F(1))X'
            r'+O\bigl(\sqrt X(\log X)^3(\log\log X)^2\bigr).\]'
            r'This is the residue form of \cite[Corollary~2]{kuehleitnerNowak2004}. '
            r'The removal of the factor at $3$ and the comparison with the original '
            r'count are proved in Lean.'),
    }
    for label in graph:
        if not label.startswith('cite:'):
            continue
        title, body = cited_notes[label]
        decl = data['cited_black_boxes'][label]['target']['declaration']
        text += [r'\begin{citedtheorem}[' + title + ']',
                 r'\label{' + safe_label(label) + '}', r'\lean{' + decl + '}',
                 r'\leanok', body, r'\end{citedtheorem}']
    text.append(r'\input{references}')
    (SRC / 'content.tex').write_text('\n\n'.join(text) + '\n')
    print(f'Wrote {len(order)} current-paper nodes, {len(helpers)} shared lemmas, '
          f'and {len(cited_notes)} literature inputs.')


if __name__ == '__main__':
    main()
