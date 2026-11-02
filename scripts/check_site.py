#!/usr/bin/env python3
"""Check a generated site's inputs, declaration links, and local resources."""

import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit
from blueprint_dependencies import blueprint_roots, hashes_digest, validate_graph
from render_content import safe_label

ROOT = Path(__file__).resolve().parents[1]


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        if tag == 'a' and 'name' in attrs:
            self.ids.add(attrs['name'])
        for key in ('href', 'src'):
            if key in attrs:
                self.links.append(attrs[key])


def reachable(graph, root):
    seen, pending = set(), list(graph[root])
    while pending:
        node = pending.pop()
        if node not in seen:
            seen.add(node)
            pending.extend(graph[node])
    return seen


def main():
    manifest = json.loads((ROOT / 'blueprint/build-manifest.json').read_text())
    errors = []
    graph = json.loads((ROOT / 'blueprint/dependencies.json').read_text())
    evidence = json.loads((ROOT / 'blueprint/dependency-evidence.json').read_text())
    roots = blueprint_roots()
    validate_graph(graph)
    if set(graph) != set(roots) or evidence['roots'] != roots:
        errors.append('Graph nodes differ from the registered results and supporting lemmas')
    if evidence['lean_sources_digest'] != hashes_digest(manifest['lean_sources_sha256']):
        errors.append('Dependency extraction used different Lean sources')
    if set(evidence['paths']) != set(graph):
        errors.append('Missing dependency evidence')
    for label, deps in graph.items():
        paths = evidence['paths'].get(label, {})
        if set(paths) != set(deps):
            errors.append(f'Dependency evidence differs for {label}')
        for dep, path in paths.items():
            if (len(path) < 2 or path[0] != roots[label] or path[-1] != roots[dep]
                    or any(n in roots.values() for n in path[1:-1])):
                errors.append(f'Invalid dependency path: {label} to {dep}')
    for group in ('lean_sources_sha256', 'blueprint_inputs_sha256'):
        if not manifest.get(group):
            raise ValueError(f'Missing manifest group {group}')
        for filename, expected in manifest[group].items():
            path = ROOT / filename
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                errors.append(f'Changed build input: {filename}')
    html_files = [ROOT / 'index.html', *(ROOT / 'blueprint').glob('*.html')]
    parsed = {}
    for path in html_files:
        parser = Links()
        content = path.read_text()
        if path.name == 'dep_graph_document.html':
            dot = content.split('.renderDot(', 1)[-1]
            if re.search(r'\ba[0-9]{6,}\s*\[', dot):
                errors.append('Anonymous theorem node in the dependency graph')
            nodes = set(re.findall(r'"([^"\n]+)"\s*\[', dot))
            if nodes != {safe_label(k) for k in graph}:
                errors.append('Rendered graph nodes differ from extracted dependencies')
            else:
                rendered = {n: set() for n in nodes}
                for dependency, result in re.findall(r'"([^"\n]+)" -> "([^"\n]+)"', dot):
                    rendered[result].add(dependency)
                expected = {safe_label(k): {safe_label(d) for d in ds}
                            for k, ds in graph.items()}
                # Graphviz removes redundant arrows; all dependency paths must remain.
                if any(reachable(rendered, n) != reachable(expected, n) for n in nodes):
                    errors.append('Rendered graph changed the extracted dependency paths')
        parser.feed(content)
        parsed[path.resolve()] = parser
        if '/find/#doc/' in content:
            errors.append(f'Unresolved Lean documentation URL: {path.relative_to(ROOT)}')
        if 'project-links' not in content or 'theme-toggle' not in content:
            errors.append(f'Missing navigation: {path.relative_to(ROOT)}')
    count = 0
    for page, parser in parsed.items():
        for href in parser.links:
            url = urlsplit(href)
            if url.scheme or url.netloc or href.startswith('//'):
                continue
            target = (page.parent / unquote(url.path)).resolve() if url.path else page
            if target.is_dir():
                target /= 'index.html'
            if not target.is_relative_to(ROOT) or not target.is_file():
                errors.append(f'Broken local link in {page.name}: {href}')
                continue
            if url.fragment and target in parsed and target.name != 'dep_graph_document.html':
                if unquote(url.fragment) not in parsed[target].ids:
                    errors.append(f'Missing anchor in {page.name}: {href}')
            count += 1
    revision = manifest['lean_source_revision']
    if not re.fullmatch('[0-9a-f]{40}', revision):
        errors.append('Source revision is not an exact commit')
    for name, url in manifest['source_links'].items():
        if f'/blob/{revision}/formalization/' not in url:
            errors.append(f'Unpinned source link: {name}')
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'Checked {len(html_files)} pages, {count} local links, '
          f'{len(manifest["source_links"])} declaration links, and source hashes.')


if __name__ == '__main__':
    main()
