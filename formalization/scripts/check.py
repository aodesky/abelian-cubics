#!/usr/bin/env python3
"""Audit paper alignment, build the library, and check transitive proof axioms."""

import argparse
from collections import Counter
import difflib
import json
import os
from pathlib import Path
import subprocess
import sys

from paper import statements


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "results.json"


def proof_file_checks(entries: dict, root: Path) -> tuple[list[str], list[str]]:
    """Require distinct, real source files for completed paper proofs.

    Lean checks the declarations' defining modules, so naming a wrapper that
    merely imports a proof cannot satisfy the proof-file mapping.
    """
    errors, checks, owners = [], [], {}
    for label, entry in entries.items():
        if entry["status"] != "proved":
            continue
        filename = entry.get("proof_file")
        path = Path(filename) if isinstance(filename, str) else None
        if (path is None or path.suffix != ".lean" or path.is_absolute() or
                not path.parts or path.parts[0] != "Cubic" or
                not all(part.isidentifier() for part in path.with_suffix("").parts)):
            errors.append(f"Missing or invalid proof file for completed result: {label}")
            continue
        if not (root / path).is_file():
            errors.append(f"Proof file does not exist for {label}: {path}")
        if path in owners:
            errors.append(f"Completed paper results share a proof file: {owners[path]}, {label}")
        owners[path] = label
        module = ".".join(path.with_suffix("").parts)
        for declaration in entry["declarations"]:
            checks.append(
                "open Lean Elab Command in\nrun_cmd do\n"
                "  let env ← getEnv\n"
                f"  let some actual := env.getModuleIdxFor? ``{declaration}\n"
                '    | throwError "Proof declaration has no defining module"\n'
                f"  let some expected := env.getModuleIdx? `{module}\n"
                '    | throwError "Registered proof module is not imported"\n'
                "  unless actual == expected do\n"
                f'    throwError "Wrong defining module for {declaration}: expected {module}"')
    return errors, checks


def target_checks(label: str, entry: dict, entries: dict | None = None) -> tuple[list[str], list[str]]:
    """Keep a parameterized template distinct from a concrete proposition and proof.

    The generated Lean checks verify types, not correspondence to the manuscript.
    Canonical local data and the mathematical interpretation still require review.
    """
    target = entry.get("target")
    if target is None:
        if entry.get("status") == "proved":
            return [f"A proved result must have a concrete target and proof: {label}"], []
        return [], []
    errors, checks = [], []
    kind = target.get("kind")
    declaration = target.get("declaration")
    context = target.get("context")
    proof = target.get("proof")
    prerequisite = target.get("prerequisite")
    conditional_proof = target.get("conditional_proof")
    assumptions = target.get("black_box_assumptions", [])
    assumption_declarations = []
    if not isinstance(assumptions, list) or not all(isinstance(a, str) for a in assumptions):
        errors.append(f"Black-box assumptions must be a list of registered labels: {label}")
        assumptions = []
    if assumptions and kind != "concrete":
        errors.append(f"Only concrete targets may list black-box assumptions: {label}")
    if len(set(assumptions)) != len(assumptions):
        errors.append(f"Duplicate black-box assumption: {label}")
    for assumption in assumptions:
        source = (entries or {}).get(assumption, {}).get("target", {})
        authorization = source.get("authorized_by_user")
        name = source.get("declaration")
        if (source.get("kind") != "black_box" or not isinstance(authorization, str)
                or not authorization.strip()):
            errors.append(f"Unregistered or unauthorized black-box assumption for {label}: {assumption}")
        elif (not isinstance(name, str) or not name.startswith(("Cubic.", "CubicTargets."))
                or any(c in name for c in "\n\r")):
            errors.append(f"Invalid black-box declaration for {label}: {assumption}")
        else:
            assumption_declarations.append(name)
    for name in (declaration, context, proof, prerequisite, conditional_proof):
        if name is not None and (not isinstance(name, str) or
                not name.startswith(("Cubic.", "CubicTargets.")) or
                any(c in name for c in "\n\r")):
            errors.append(f"Invalid target declaration for {label}: {name!r}")
    if not declaration:
        errors.append(f"Missing target declaration: {label}")
    if kind == "schema":
        if not context:
            errors.append(f"Missing schema context: {label}")
        if entry["status"] == "proved" or proof is not None:
            errors.append(f"A statement schema cannot certify a paper result: {label}")
        checks.append(f"example : {context} → Prop := {declaration}")
        if bool(prerequisite) != bool(conditional_proof):
            errors.append(f"Conditional proofs must name their prerequisite: {label}")
        if prerequisite and conditional_proof:
            if conditional_proof not in entry["declarations"]:
                errors.append(f"Conditional proof missing from coverage: {label}")
            checks.append(f"example : ∀ D : {context}, {prerequisite} D → {declaration} D := "
                          f"@{conditional_proof}")
    elif kind == "black_box":
        if context is not None or prerequisite or conditional_proof:
            errors.append(f"Black-box statements must bind their full setup: {label}")
        if entry["status"] == "proved" or proof is not None:
            errors.append(f"An assumed black box cannot certify a paper result: {label}")
        checks.append(f"example : Prop := {declaration}")
    elif kind == "concrete":
        if context is not None:
            errors.append(f"Concrete targets must bind their canonical data: {label}")
        if prerequisite or conditional_proof:
            errors.append(f"Concrete targets cannot conceal an unproved prerequisite: {label}")
        checks.append(f"example : Prop := {declaration}")
        if entry["status"] == "proved" and not proof:
            errors.append(f"Missing proof of the concrete target: {label}")
        if proof:
            if entry["status"] != "proved" or proof not in entry["declarations"]:
                errors.append(f"Target proof is inconsistent with registry coverage: {label}")
            proof_type = " → ".join([*assumption_declarations, declaration])
            checks.append(f"example : {proof_type} := {proof}")
    else:
        errors.append(f"Invalid target kind: {label}")
    return errors, checks


def supporting_declaration_checks(label: str, entry: dict) -> list[str]:
    """Supporting lemmas from other modules, recorded for traceability.

    They are type-checked with the registry but, unlike `declarations`, are exempt from
    the proof-file rule, so they cannot be what certifies a completed result.
    """
    names = entry.get("supporting_declarations", [])
    if not isinstance(names, list):
        return [f"Supporting declarations must be a list: {label}"]
    errors = []
    for name in names:
        if (not isinstance(name, str) or not name.startswith("Cubic.")
                or any(c in name for c in "\n\r")):
            errors.append(f"Invalid supporting declaration name for {label}: {name!r}")
    if len(set(map(str, names))) != len(names):
        errors.append(f"Duplicate supporting declaration: {label}")
    overlap = set(map(str, names)) & set(entry.get("declarations", []))
    if overlap:
        errors.append(f"Supporting declarations repeat main declarations for {label}: "
                      + ", ".join(sorted(overlap)))
    return errors


def cited_black_box_checks(cited: object) -> tuple[list[str], list[str]]:
    """Validate black boxes that quote a cited theorem rather than a paper label.

    They carry no status and cannot certify anything themselves; a proved label may
    only list one as an assumption, and it stays in that proof's checked type.
    """
    errors, checks = [], []
    if not isinstance(cited, dict):
        return ["Cited black boxes must be a mapping"], []
    for key, entry in cited.items():
        target = entry.get("target", {}) if isinstance(entry, dict) else {}
        name = target.get("declaration")
        authorization = target.get("authorized_by_user")
        if not isinstance(key, str) or not key.startswith("cite:"):
            errors.append(f"Cited black-box keys must start with 'cite:': {key!r}")
        if (not isinstance(entry, dict) or not isinstance(entry.get("source"), str)
                or not entry["source"].strip() or not isinstance(entry.get("statement"), str)
                or not entry["statement"].strip()):
            errors.append(f"Cited black box must quote its source statement: {key}")
        if target.get("kind") != "black_box":
            errors.append(f"Cited entries must be black boxes: {key}")
        if not isinstance(authorization, str) or not authorization.strip():
            errors.append(f"Cited black box lacks user authorization: {key}")
        if any(target.get(field) is not None
               for field in ("context", "proof", "prerequisite", "conditional_proof")):
            errors.append(f"Black-box statements must bind their full setup: {key}")
        if not isinstance(entry, dict) or "status" in entry or entry.get("declarations"):
            errors.append(f"Cited black boxes cannot carry proof status: {key}")
        if (not isinstance(name, str) or not name.startswith(("Cubic.", "CubicTargets."))
                or any(c in name for c in "\n\r")):
            errors.append(f"Invalid black-box declaration for {key}: {name!r}")
        else:
            checks.append(f"example : Prop := {name}")
    return errors, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry", type=Path, default=REGISTRY,
                        help="registry for another manuscript (default: results.json)")
    parser.add_argument("--paper-only", action="store_true")
    parser.add_argument("--show", metavar="LABEL", help="show a current TeX statement")
    parser.add_argument(
        "--refresh", metavar="LABEL", nargs="+",
        help="accept specified statement snapshots AFTER manually reviewing the Lean alignment",
    )
    args = parser.parse_args()
    data = json.loads(args.registry.read_text())
    paper = (ROOT / data["paper"]).resolve()
    current = statements(paper.read_text())
    entries = data["results"]
    if args.show:
        item = current[args.show]
        print(f"{paper}:{item.line}\n{item.text}")
        return 0
    if args.refresh:
        for label in args.refresh:
            if label not in entries or label not in current:
                raise ValueError(f"Cannot refresh unregistered or missing label: {label}")
        for label in args.refresh:
            entries[label]["statement"] = current[label].text
        args.registry.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
        print("Refreshed reviewed statement snapshots: " + ", ".join(args.refresh))
        return 0

    errors = []
    statement_checks = []
    cited = data.get("cited_black_boxes", {})
    cited_errors, cited_checks = cited_black_box_checks(cited)
    errors.extend(cited_errors)
    statement_checks.extend(cited_checks)
    assumption_sources = {**entries, **(cited if isinstance(cited, dict) else {})}
    for label in sorted(current.keys() - entries.keys()):
        errors.append(f"Unregistered mathematical label: {label}")
    for label in sorted(entries.keys() - current.keys()):
        errors.append(f"Missing or renamed mathematical label: {label}")
    for label in entries.keys() & current.keys():
        entry = entries[label]
        if entry["statement"] != current[label].text:
            errors.append(f"Statement changed; review {label} at {paper}:{current[label].line}")
            print("\n".join(difflib.unified_diff(
                [entry["statement"]], [current[label].text],
                fromfile="reviewed statement", tofile="current statement", lineterm="",
            )))
        if entry["status"] not in {"planned", "supporting", "proved"}:
            errors.append(f"Invalid status: {label}")
        if entry["status"] in {"supporting", "proved"} and not entry["declarations"]:
            errors.append(f"Missing Lean declarations for {label}")
        for declaration in entry["declarations"]:
            if not declaration.startswith("Cubic.") or any(c in declaration for c in "\n\r"):
                errors.append(f"Invalid declaration name: {declaration!r}")
        errors.extend(supporting_declaration_checks(label, entry))
        if entry["role"] not in {"essential", "nonessential"}:
            errors.append(f"Invalid role: {label}")
        if not 1 <= entry["stage"] <= 7:
            errors.append(f"Invalid stage: {label}")
        if entry["role"] == "nonessential" and entry["stage"] != 7:
            errors.append(f"Nonessential work must follow essential targets: {label}")
        target_errors, checks = target_checks(label, entry, assumption_sources)
        errors.extend(target_errors)
        statement_checks.extend(checks)
    proof_errors, file_checks = proof_file_checks(entries, ROOT)
    errors.extend(proof_errors)
    # Require every source module to be reachable from the public root import.
    roots = ("Cubic", "CubicTargets")
    files = {name: ROOT / f"{name}.lean" for name in roots}
    for name in roots:
        files.update({".".join(p.relative_to(ROOT).with_suffix("").parts): p
                      for p in (ROOT / name).rglob("*.lean")})
    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        for line in files[module].read_text().splitlines():
            if line.startswith(("import Cubic.", "import CubicTargets.")):
                dependency = line.split()[1]
                if dependency not in files:
                    errors.append(f"Missing source module: {dependency}")
                else:
                    visit(dependency)

    for name in roots:
        visit(name)
    errors.extend(f"Module omitted from root imports: {m}" for m in files.keys() - visited)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    counts = Counter(entry["status"] for entry in entries.values())
    print(f"Paper audit passed: {len(entries)} labels; " +
          ", ".join(f"{counts[s]} {s}" for s in ("proved", "supporting", "planned")), flush=True)
    relative = sum(entry["status"] == "proved" and
                   bool(entry.get("target", {}).get("black_box_assumptions"))
                   for entry in entries.values())
    if relative:
        print(f"Of the proved labels, {relative} retain explicitly authorized black-box inputs.",
              flush=True)
    if args.paper_only:
        return 0

    lake = os.environ.get("LAKE", "lake")
    subprocess.run([lake, "build"], cwd=ROOT, check=True)
    subprocess.run([lake, "env", "lean", "Audit.lean"], cwd=ROOT, check=True)
    declarations = sorted({d for entry in entries.values()
                           for d in [*entry["declarations"],
                                     *entry.get("supporting_declarations", [])]})
    audit = ROOT / ".lake" / "RegistryAudit.lean"
    audit.write_text("import Cubic\nimport CubicTargets\nimport Lean\n" +
                     "\n".join([*(f"#check {d}" for d in declarations),
                                *statement_checks, *file_checks]) + "\n")
    checked = subprocess.run([lake, "env", "lean", str(audit)], cwd=ROOT,
                             text=True, capture_output=True)
    if checked.returncode:
        print(checked.stdout + checked.stderr, file=sys.stderr)
        return checked.returncode
    print(f"Registry audit passed: {len(declarations)} proof references resolve; "
          f"{len(statement_checks)} target type checks and "
          f"{len(file_checks)} proof-file checks passed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f"Audit failed: {error}", file=sys.stderr)
        sys.exit(1)
