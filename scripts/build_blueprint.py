#!/usr/bin/env python3
"""Build the Lean blueprint and publish its static files into blueprint/.

Install blueprint/requirements.txt and Graphviz first. The renderer is the
standard leanblueprint plasTeX plugin, invoked directly because this repository
keeps its Lake project in formalization/ rather than at the repository root.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from site_navigation import add_blueprint_navigation
from blueprint_dependencies import check_project_sources, source_hashes


ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT = ROOT / "blueprint"
SOURCE = BLUEPRINT / "src"
LEAN = ROOT / "formalization"
DOC_BASE = "https://aodesky.github.io/abelian-cubics/blueprint/lean"
REPOSITORY = "https://github.com/aodesky/abelian-cubics"
# The Lean sources the blueprint links into.
SOURCES = ["formalization/Cubic", "formalization/Cubic.lean",
           "formalization/CubicTargets", "formalization/CubicTargets.lean"]


def declaration_locations():
    """Index public declaration headers and their enclosing namespaces."""
    locations = {}
    for path in sorted([*(LEAN / "Cubic").rglob("*.lean"), *(LEAN / "CubicTargets").rglob("*.lean")]):
        scopes = []
        for number, line in enumerate(path.read_text().splitlines(), 1):
            scope = re.match(r"^(namespace|section)\s*(\S*)", line)
            if scope:
                scopes.append((scope[1], scope[2]))
                continue
            if re.match(r"^end(?:\s|$)", line):
                if scopes:
                    scopes.pop()
                continue
            declaration = re.match(
                r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|private)\s+)*"
                r"(?:theorem|lemma|def|structure|abbrev|inductive|class)\s+((?:[^\s(:«]|«[^»]*»)+)", line)
            if declaration:
                namespace = [name for kind, name in scopes if kind == "namespace"]
                name = ".".join([*namespace, declaration[1]])
                if name in locations:
                    raise ValueError(f"Duplicate declaration: {name}")
                locations[name] = (path.relative_to(ROOT).as_posix(), number)
    return locations


def blueprint_declarations():
    text = (SOURCE / "content.tex").read_text()
    declarations = sorted({name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", text)
                           for name in group.split(",")})
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    if len(set(labels)) != len(labels):
        raise ValueError("Duplicate blueprint labels")
    for group in re.findall(r"\\uses\{([^}]+)\}", text):
        for label in group.split(","):
            if label.strip() not in labels:
                raise ValueError(f"Unknown dependency: {label}")
    return declarations, labels


def check_declarations(project, declarations):
    check_project_sources(project)
    lake = os.environ.get("LAKE", "lake")
    checks = "import Cubic\nimport CubicTargets\n" + "\n".join(f"#check {name}" for name in declarations) + "\n"
    with tempfile.TemporaryDirectory(prefix="blueprint-check-") as directory:
        path = Path(directory) / "BlueprintCheck.lean"
        path.write_text(checks)
        subprocess.run([lake, "env", "lean", str(path)], cwd=project, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def check_lean(project, declarations):
    check_project_sources(project)
    lake = os.environ.get("LAKE", "lake")
    subprocess.run([lake, "build"], cwd=project, check=True)
    check_declarations(project, declarations)
    subprocess.run([lake, "env", "lean", "Audit.lean"],
                   cwd=project, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-project", type=Path, default=LEAN,
                        help="Matching built Lean project (default: formalization/)")
    parser.add_argument("--plastex", default="plastex")
    parser.add_argument("--preview", action="store_true",
                        help="Preview uncommitted sources; not suitable for deployment")
    parser.add_argument("--reuse-lean-check", action="store_true",
                        help="Reuse a previous successful check of identical Lean inputs")
    args = parser.parse_args()
    executable = shutil.which(args.plastex)
    if executable is None:
        raise FileNotFoundError(f"plasTeX executable not found: {args.plastex}")
    executable = str(Path(executable).resolve())
    subprocess.run(["python3", str(ROOT / "scripts/render_content.py")], check=True)
    declarations, labels = blueprint_declarations()
    locations = declaration_locations()
    for name in declarations:
        if name not in locations:
            raise ValueError(f"Declaration not found in public Lean sources: {name}")
    if args.reuse_lean_check:
        previous = json.loads((BLUEPRINT / "build-manifest.json").read_text())
        hashes = source_hashes()
        if hashes != previous.get("lean_sources_sha256"):
            raise ValueError("Lean inputs changed: run a fresh Lean check")
        added = set(declarations) - set(previous["source_links"])
        if added:
            check_declarations(args.lean_project.resolve(), sorted(added))
            print(f'Checked {len(added)} additional declarations; reused the full '
                  'build and axiom audit for unchanged Lean sources.')
    else:
        check_lean(args.lean_project.resolve(), declarations)
    revision = "main" if args.preview else subprocess.check_output(
        ["git", "log", "-1", "--format=%H", "--", *SOURCES],
        cwd=ROOT, text=True).strip()
    # Refuse to publish links to a committed source different from the local one.
    if not args.preview:
        subprocess.run(["git", "diff", "--exit-code", revision, "--", *SOURCES],
                       cwd=ROOT, check=True, stdout=subprocess.PIPE)
    environment = os.environ.copy()
    environment["PATH"] = str(Path(executable).parent) + os.pathsep + environment["PATH"]
    subprocess.run([executable, "-c", "plastex.cfg", "web.tex"], cwd=SOURCE,
                   env=environment, check=True)
    output = BLUEPRINT / "web"
    if not (output / "index.html").is_file() or not (output / "dep_graph_document.html").is_file():
        raise RuntimeError("Renderer did not produce the blueprint and dependency graph")
    # Convert doc-gen lookup URLs into exact, revision-pinned source links.
    links = {f"{DOC_BASE}/find/#doc/{name}":
             f"{REPOSITORY}/blob/{revision}/{locations[name][0]}#L{locations[name][1]}"
             for name in declarations}
    for path in output.rglob("*"):
        if path.is_file() and path.suffix in {".html", ".json", ".js", ".svg"}:
            text = path.read_text()
            for old in sorted(links, key=len, reverse=True):
                text = text.replace(old, links[old])
            if path.suffix == ".html":
                text = add_blueprint_navigation(text)
            if path.name == "dep_graph_document.html":
                # Long declaration names make a top-down graph excessively wide.
                text = text.replace('graph [bgcolor=transparent];',
                                    'graph [bgcolor=transparent, rankdir=LR, '
                                    'nodesep=0.25, ranksep=0.7];', 1)
            path.write_text(text)
    for path in output.iterdir():
        destination = BLUEPRINT / path.name
        if path.is_dir():
            shutil.copytree(path, destination, dirs_exist_ok=True)
        else:
            shutil.copyfile(path, destination)
    manifest = {
        "lean_source_revision": revision,
        "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "nodes": len(re.findall(r"\\lean\{", (SOURCE / "content.tex").read_text())),
        "declarations": len(declarations),
        "checks": ["lake build", "all blueprint declarations exist", "standard axioms only"],
        "source_sha256": hashlib.sha256((SOURCE / "content.tex").read_bytes()).hexdigest(),
        "blueprint_inputs_sha256": {
            path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [*SOURCE.glob("*.tex"), *SOURCE.glob("*.json"),
                         *SOURCE.glob("*.css"), SOURCE / "plastex.cfg",
                         BLUEPRINT / "dependencies.json", BLUEPRINT / "dependency-evidence.json",
                         BLUEPRINT / "order.json",
                         LEAN / "results.json"]
        },
        "lean_sources_sha256": source_hashes(),
        "source_links": {name: links[f"{DOC_BASE}/find/#doc/{name}"] for name in declarations},
    }
    (BLUEPRINT / "build-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Built {manifest['nodes']} blueprint nodes with {len(declarations)} checked Lean declarations.")


if __name__ == "__main__":
    main()
