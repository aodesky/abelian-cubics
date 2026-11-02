#!/usr/bin/env python3
"""Extract dependencies between registered results from elaborated Lean proofs.

Follow project helpers until another registered proof or literature input is
reached. Imports alone never create graph edges. Run after `lake build`.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def extract(project):
    registry = json.loads((ROOT / 'formalization/results.json').read_text())
    entries = {**registry['results']}
    used = {a for e in entries.values()
            for a in e.get('target', {}).get('black_box_assumptions', [])}
    entries.update({k: v for k, v in registry['cited_black_boxes'].items() if k in used})
    roots = {k: e['target'].get('proof') or e['target']['declaration']
             for k, e in entries.items()}
    pairs = ',\n'.join('    (' + json.dumps(k) + ', ``' + v + ')' for k, v in roots.items())
    source = '''import Cubic
import CubicTargets
import Lean
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let entries : Array (String × Name) := #[
PAIRS
  ]
  let isProject := fun name => match env.getModuleFor? name with
    | some m => (`Cubic).isPrefixOf m || (`CubicTargets).isPrefixOf m
    | none => false
  let mut cache : NameMap (Array Name) := {}
  for (label, root) in entries do
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut found : Array String := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n != root then
        if let some (other, _) := entries.find? (fun p => p.2 == n) then
          found := found.push other
          continue
      let cs ← if let some cs := cache.find? n then pure cs else do
        let some ci := env.find? n | throwError "Missing declaration {n}"
        let cs := (ci.getUsedConstantsAsSet.toList.filter isProject).toArray
        cache := cache.insert n cs
        pure cs
      for c in cs do pending := pending.push c
    liftIO <| IO.println (Json.compress (toJson (label, found)))
'''.replace('PAIRS', pairs)
    with tempfile.TemporaryDirectory(prefix='cubic-blueprint-') as directory:
        path = Path(directory) / 'Dependencies.lean'
        path.write_text(source)
        result = subprocess.run([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(path)],
                                cwd=project, text=True, capture_output=True, check=True)
    graph = {}
    for line in result.stdout.splitlines():
        if line.startswith('['):
            label, deps = json.loads(line)
            graph[label] = sorted(set(deps))
    if set(graph) != set(roots):
        raise ValueError('Incomplete dependency extraction')
    # Validate acyclicity before asking the renderer to draw the graph.
    done = set()
    def visit(label, ancestors):
        if label in ancestors:
            raise ValueError(f'Cycle at {label}')
        if label not in done:
            for dep in graph[label]:
                visit(dep, ancestors | {label})
            done.add(label)
    for label in graph:
        visit(label, set())
    (ROOT / 'blueprint/dependencies.json').write_text(json.dumps(graph, indent=2) + '\n')
    print(f'Extracted dependencies for {len(graph)} nodes.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-project', type=Path, default=ROOT / 'formalization')
    extract(parser.parse_args().lean_project.resolve())
