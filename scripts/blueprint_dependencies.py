#!/usr/bin/env python3
"""Extract blueprint dependencies from elaborated Lean declarations.

Expose the paper results, literature inputs, and selected shared lemmas. Follow
other project helpers until an exposed declaration is reached. Imports alone
never create graph edges. Run after `lake build`.
"""

import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'formalization'


def source_files():
    return [LEAN / name for name in ('Cubic.lean', 'CubicTargets.lean',
            'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'Audit.lean')] + [
            *(LEAN / 'Cubic').rglob('*.lean'), *(LEAN / 'CubicTargets').rglob('*.lean')]


def source_hashes():
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in source_files()}


def hashes_digest(hashes):
    return hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()


def check_project_sources(project):
    for path in source_files():
        other = project / path.relative_to(LEAN)
        if not other.is_file() or other.read_bytes() != path.read_bytes():
            raise ValueError(f'Lean check project differs from public source: {other}')


def normalize(name):
    return name.replace('«', '').replace('»', '')


def blueprint_roots():
    registry = json.loads((LEAN / 'results.json').read_text())
    entries = dict(registry['results'])
    used = {a for e in entries.values()
            for a in e.get('target', {}).get('black_box_assumptions', [])}
    entries.update({k: v for k, v in registry['cited_black_boxes'].items() if k in used})
    roots = {k: normalize(e['target'].get('proof') or e['target']['declaration'])
             for k, e in entries.items()}
    helpers = json.loads((ROOT / 'blueprint/src/helpers.json').read_text())
    roots.update({k: normalize(e['declaration']) for k, e in helpers.items()})
    if len(set(roots.values())) != len(roots):
        raise ValueError('Two blueprint nodes have the same declaration')
    return roots


def validate_graph(graph):
    done = set()
    def visit(label, ancestors):
        if label not in graph:
            raise ValueError(f'Unknown dependency: {label}')
        if label in ancestors:
            raise ValueError(f'Cycle at {label}')
        if label not in done:
            for dep in graph[label]:
                visit(dep, ancestors | {label})
            done.add(label)
    for label in graph:
        visit(label, set())


def project_graph(records, roots):
    """Collapse hidden helpers, retaining a shortest declaration path per edge."""
    names = {name: label for label, name in roots.items()}
    graph, paths = {}, {}
    for label, root in roots.items():
        pending = deque([root])
        parent = {root: None}
        found = {}
        while pending:
            name = pending.popleft()
            if name not in records:
                raise ValueError(f'Missing declaration: {name}')
            if name != root and name in names:
                path, cursor = [], name
                while cursor is not None:
                    path.append(cursor)
                    cursor = parent[cursor]
                found[names[name]] = path[::-1]
                continue
            for dep in sorted(records[name]['deps']):
                if dep not in parent:
                    parent[dep] = name
                    pending.append(dep)
        graph[label] = sorted(found)
        paths[label] = {k: found[k] for k in sorted(found)}
    validate_graph(graph)
    return graph, paths


EXPORT = '''import Cubic
import CubicTargets
import Lean
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isProject := fun name => match env.getModuleFor? name with
    | some m => (`Cubic).isPrefixOf m || (`CubicTargets).isPrefixOf m
    | none => false
  for (name, ci) in env.constants.toList do
    if isProject name then
      let deps := (ci.getUsedConstantsAsSet.toList.filter isProject).map Name.toString
      liftIO <| IO.println (Json.compress (toJson (name.toString, deps)))
'''


def extract(project, cache=None):
    check_project_sources(project)
    hashes = source_hashes()
    if cache and cache.exists():
        saved = json.loads(cache.read_text())
        if saved['lean_sources_sha256'] != hashes:
            raise ValueError('Dependency cache is stale: remove it and extract again')
        records = saved['records']
    else:
        with tempfile.TemporaryDirectory(prefix='cubic-blueprint-') as directory:
            path = Path(directory) / 'Dependencies.lean'
            path.write_text(EXPORT)
            result = subprocess.run([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(path)],
                                    cwd=project, text=True, capture_output=True, check=True)
        records = {}
        for line in result.stdout.splitlines():
            if line.startswith('['):
                name, deps = json.loads(line)
                records[normalize(name)] = {'deps': sorted(normalize(d) for d in deps)}
        if cache:
            cache.write_text(json.dumps({'lean_sources_sha256': hashes, 'records': records}))
    roots = blueprint_roots()
    graph, paths = project_graph(records, roots)
    (ROOT / 'blueprint/dependencies.json').write_text(json.dumps(graph, indent=2) + '\n')
    evidence = {'lean_sources_digest': hashes_digest(hashes), 'roots': roots, 'paths': paths}
    (ROOT / 'blueprint/dependency-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    used = {n for ds in graph.values() for n in ds}
    isolated = [k for k, ds in graph.items() if not ds and k not in used]
    print(f'Extracted {len(graph)} nodes, {sum(map(len, graph.values()))} dependencies, '
          f'and {len(isolated)} isolated nodes.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-project', type=Path, default=LEAN)
    parser.add_argument('--constant-cache', type=Path,
                        help='Reuse exported constants only for identical Lean sources')
    args = parser.parse_args()
    extract(args.lean_project.resolve(), args.constant_cache)
