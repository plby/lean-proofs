#!/usr/bin/env python3
"""Extract and remap the initial clauses used by each trimmed LRAT proof."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_lrat(path: Path):
    rows = []
    with path.open(encoding="ascii") as stream:
        for line in stream:
            fields = line.split()
            assert fields and fields[1] != "d"
            first_zero = fields.index("0")
            assert fields[-1] == "0"
            rows.append((fields, first_zero))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "reduced")
    args = parser.parse_args()
    output = args.output.resolve()
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="ascii"))
    base = (HERE / "base.clauses").read_text(encoding="ascii").splitlines()
    assert len(base) == manifest["base_clause_count"]
    output.mkdir(parents=True, exist_ok=True)
    reduced_cases = []

    for case in manifest["cases"]:
        name = case["name"]
        units = (HERE / "cases" / f"{name}.units").read_text(
            encoding="ascii"
        ).splitlines()
        original_clauses = base + units
        assert len(original_clauses) == case["initial_clauses"]
        rows = parse_lrat(HERE / "cases" / f"{name}.lrat")

        used = set()
        for fields, first_zero in rows:
            for text in fields[first_zero + 1:-1]:
                hint = abs(int(text))
                if hint <= case["initial_clauses"]:
                    used.add(hint)
        retained = sorted(used)
        remap = {old: new for new, old in enumerate(retained, 1)}

        cnf = output / f"{name}.cnf"
        with cnf.open("w", encoding="ascii", newline="\n") as stream:
            stream.write(f"p cnf 286 {len(retained)}\n")
            for old in retained:
                stream.write(original_clauses[old - 1] + "\n")

        proof = output / f"{name}.lrat"
        with proof.open("w", encoding="ascii", newline="\n") as stream:
            for fields, first_zero in rows:
                for i in range(first_zero + 1, len(fields) - 1):
                    hint = int(fields[i])
                    if abs(hint) <= case["initial_clauses"]:
                        mapped = remap[abs(hint)]
                        fields[i] = str(mapped if hint > 0 else -mapped)
                stream.write(" ".join(fields) + "\n")

        ids = output / f"{name}.ids"
        ids.write_text(
            " ".join(map(str, retained)) + "\n", encoding="ascii", newline="\n"
        )
        reduced_cases.append({
            "name": name,
            "original_initial_clauses": case["initial_clauses"],
            "reduced_initial_clauses": len(retained),
            "original_initial_ids": retained,
            "base_ids": sum(old <= 16830 for old in retained),
            "unit_ids": sum(old > 16830 for old in retained),
            "cnf_bytes": cnf.stat().st_size,
            "cnf_sha256": digest(cnf),
            "lrat_bytes": proof.stat().st_size,
            "lrat_sha256": digest(proof),
            "ids_sha256": digest(ids),
        })

    reduced_manifest = {
        "schema": 1,
        "source_manifest_sha256": digest(HERE / "manifest.json"),
        "variable_count": 286,
        "case_count": len(reduced_cases),
        "clause_id_semantics": {
            "homogeneous_four": [1, 990],
            "triple_forward": [991, 1430],
            "four_triple_partition": [1431, 16830],
            "case_units_begin": 16831,
        },
        "total_cnf_bytes": sum(case["cnf_bytes"] for case in reduced_cases),
        "total_lrat_bytes": sum(case["lrat_bytes"] for case in reduced_cases),
        "max_initial_clauses": max(
            case["reduced_initial_clauses"] for case in reduced_cases
        ),
        "max_lrat_bytes": max(case["lrat_bytes"] for case in reduced_cases),
        "cases": reduced_cases,
    }
    (output / "manifest.json").write_text(
        json.dumps(reduced_manifest, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )
    print(f"cases={len(reduced_cases)}")
    print(f"total_cnf_bytes={reduced_manifest['total_cnf_bytes']}")
    print(f"total_lrat_bytes={reduced_manifest['total_lrat_bytes']}")
    print(f"max_initial_clauses={reduced_manifest['max_initial_clauses']}")


if __name__ == "__main__":
    main()
