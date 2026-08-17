#!/usr/bin/env python3
"""Reconstruct the shared D12 clauses, case units, and optional full DIMACS."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
N = 12
EDGES = list(itertools.combinations(range(N), 2))
TRIPLES = list(itertools.combinations(range(N), 3))
EDGE_VAR = {e: i + 1 for i, e in enumerate(EDGES)}
HOM_VAR = {t: len(EDGES) + i + 1 for i, t in enumerate(TRIPLES)}


def canonical_partitions(xs: tuple[int, ...]):
    """Enumerate unordered partitions into increasing triples canonically."""
    if not xs:
        yield ()
        return
    first = xs[0]
    for partners in itertools.combinations(xs[1:], 2):
        block = (first, *partners)
        chosen = set(block)
        rest = tuple(x for x in xs if x not in chosen)
        for tail in canonical_partitions(rest):
            yield (block, *tail)


def base_clauses() -> list[tuple[int, ...]]:
    clauses: list[tuple[int, ...]] = []
    for q in itertools.combinations(range(N), 4):
        es = tuple(EDGE_VAR[e] for e in itertools.combinations(q, 2))
        clauses.append(tuple(-x for x in es))
        clauses.append(es)
    for t in TRIPLES:
        es = tuple(EDGE_VAR[e] for e in itertools.combinations(t, 2))
        h = HOM_VAR[t]
        clauses.append((h, *(-x for x in es)))
        clauses.append((h, *es))
    partitions = list(canonical_partitions(tuple(range(N))))
    assert len(partitions) == 15400
    for part in partitions:
        clauses.append(tuple(-HOM_VAR[t] for t in part))
    assert len(clauses) == 16830
    return clauses


def clause_text(clauses) -> str:
    return "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)


def load_manifest():
    return json.loads((HERE / "manifest.json").read_text(encoding="ascii"))


def unit_clauses(case):
    return [((v,) if value else (-v,)) for v, value in case["assumptions"]]


def write_shared(manifest) -> None:
    (HERE / "base.clauses").write_text(
        clause_text(base_clauses()), encoding="ascii", newline="\n"
    )
    cases_dir = HERE / "cases"
    cases_dir.mkdir(exist_ok=True)
    for case in manifest["cases"]:
        (cases_dir / f"{case['name']}.units").write_text(
            clause_text(unit_clauses(case)), encoding="ascii", newline="\n"
        )


def write_cnf(manifest, case_name: str, output: Path) -> None:
    by_name = {case["name"]: case for case in manifest["cases"]}
    case = by_name[case_name]
    clauses = base_clauses() + unit_clauses(case)
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf 286 {len(clauses)}\n")
        stream.write(clause_text(clauses))


def write_lean_index(manifest) -> None:
    reduced = json.loads((HERE / "reduced" / "manifest.json").read_text(encoding="ascii"))
    reduced_by_name = {case["name"]: case for case in reduced["cases"]}
    modules = HERE / "Cases"
    modules.mkdir(exist_ok=True)
    imports = []

    def lean_list(items, render, chunk_size=64):
        chunks = [items[i:i + chunk_size] for i in range(0, len(items), chunk_size)]
        rendered = ["[" + ", ".join(render(item) for item in chunk) + "]" for chunk in chunks]
        return (" ++\n    ").join(rendered) if rendered else "[]"

    for case in manifest["cases"]:
        name = case["name"]
        clause_count = len(reduced_by_name[name]["original_initial_ids"])
        units_text = lean_list(
            case["assumptions"],
            lambda item: f"({item[0]}, {'true' if item[1] else 'false'})",
        )
        imports.append(f"import ErdosProblems.Erdos758.D12.Cases.{name}")
        lines = [
            "import ErdosProblems.Erdos758.D12.Semantic",
            "",
            "namespace Erdos758.D12Certificate",
            "",
            f"lrat_proof {name}_raw",
            f"  (include_str \"../reduced/{name}.cnf\")",
            f"  (include_str \"../reduced/{name}.lrat\")",
            "",
            f"def {name}_ids : String := include_str \"../reduced/{name}.ids\"",
            "",
            f"def {name}_units : List (Nat × Bool) :=\n  {units_text}",
            "",
        ]

        def emit_range(start, stop):
            theorem_name = f"{name}_sem_{start}_{stop}"
            if stop - start <= 512:
                lines.extend([
                    f"private theorem {theorem_name} (edge : Nat → Prop) :",
                    f"    d12CaseRange({name}_ids, {name}_units, edge, {start}, {stop}) := by",
                    f"  exact d12CaseRangeProof({name}_ids, {name}_units, edge, {start}, {stop})",
                    "",
                ])
                return theorem_name
            mid = start + (stop - start) // 2
            left = emit_range(start, mid)
            right = emit_range(mid, stop)
            lines.extend([
                f"private theorem {theorem_name} (edge : Nat → Prop) :",
                f"    d12CaseRange({name}_ids, {name}_units, edge, {start}, {stop}) := by",
                "  intro h",
                f"  exact h.elim ({left} edge) ({right} edge)",
                "",
            ])
            return theorem_name

        root = emit_range(0, clause_count)
        lines.extend([
            f"theorem {name} (edge : Nat → Prop) : D12Outcome edge {name}_units := by",
            f"  exact {root} edge (d12CaseRaw({name}_raw, edge))",
            "",
            "end Erdos758.D12Certificate",
            "",
        ])
        (modules / f"{name}.lean").write_text(
            "\n".join(lines), encoding="utf-8", newline="\n"
        )
    (HERE / "Certificates.lean").write_text(
        "\n".join(imports) + "\n", encoding="utf-8", newline="\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-shared", action="store_true")
    parser.add_argument("--lean-index", action="store_true")
    parser.add_argument("--cnf", metavar="CASE")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = load_manifest()
    if args.write_shared:
        write_shared(manifest)
    if args.lean_index:
        write_lean_index(manifest)
    if args.cnf:
        if args.output is None:
            parser.error("--cnf requires --output")
        write_cnf(manifest, args.cnf, args.output)
    if not args.write_shared and not args.lean_index and not args.cnf:
        parser.error("select --write-shared, --lean-index, or --cnf CASE --output FILE")


if __name__ == "__main__":
    main()
