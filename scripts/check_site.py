#!/usr/bin/env python3
"""Check a generated site's inputs, declaration links, and local resources."""

import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

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


def main():
    manifest = json.loads((ROOT / 'blueprint/build-manifest.json').read_text())
    errors = []
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
