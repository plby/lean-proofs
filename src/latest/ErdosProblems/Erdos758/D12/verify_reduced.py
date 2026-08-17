#!/usr/bin/env python3
"""Independently check the dependency-reduced D12 CNFs and RUP proofs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_clause(text: str) -> tuple[int, ...]:
    numbers = [int(x) for x in text.split()]
    assert numbers and numbers[-1] == 0
    return tuple(numbers[:-1])


def parse_cnf(path: Path):
    lines = path.read_text(encoding="ascii").splitlines()
    header = lines[0].split()
    assert header[:2] == ["p", "cnf"]
    variables, count = int(header[2]), int(header[3])
    clauses = [parse_clause(line) for line in lines[1:]]
    assert len(clauses) == count
    return variables, clauses


def parse_lrat(path: Path):
    rows = []
    with path.open(encoding="ascii") as stream:
        for line in stream:
            fields = line.split()
            assert fields and fields[1] != "d" and fields[-1] == "0"
            ident = int(fields[0])
            first_zero = fields.index("0")
            clause = tuple(int(x) for x in fields[1:first_zero])
            hints = tuple(int(x) for x in fields[first_zero + 1:-1])
            assert hints and all(hint > 0 for hint in hints)
            rows.append((ident, clause, hints))
    return rows


def rup_step(clause, hints, context, variables: int) -> None:
    assignment = [-1] * (variables + 1)
    tautology = False
    for literal in clause:
        variable = abs(literal)
        assert 1 <= variable <= variables
        value = 0 if literal > 0 else 1
        old = assignment[variable]
        if old >= 0 and old != value:
            tautology = True
            break
        assignment[variable] = value
    if tautology:
        return

    conflict = False
    for hint_index, hint in enumerate(hints):
        assert hint in context
        unassigned = []
        satisfied = False
        for literal in context[hint]:
            value = assignment[abs(literal)]
            if value < 0:
                unassigned.append(literal)
            elif bool(value) == (literal > 0):
                satisfied = True
                break
        assert not satisfied
        if not unassigned:
            assert hint_index + 1 == len(hints)
            conflict = True
            break
        assert len(unassigned) == 1
        literal = unassigned[0]
        assignment[abs(literal)] = 1 if literal > 0 else 0
    assert conflict


def verify_rup(clauses, rows, variables: int):
    context = {i: clause for i, clause in enumerate(clauses, 1)}
    hint_count = 0
    for ident, clause, hints in rows:
        assert ident not in context
        rup_step(clause, hints, context, variables)
        context[ident] = clause
        hint_count += len(hints)
    assert rows and rows[-1][1] == ()
    return len(rows), hint_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path, nargs="?", default=HERE / "reduced")
    args = parser.parse_args()
    directory = args.directory.resolve()
    source_manifest = json.loads((HERE / "manifest.json").read_text(encoding="ascii"))
    reduced = json.loads((directory / "manifest.json").read_text(encoding="ascii"))
    assert reduced["source_manifest_sha256"] == digest(HERE / "manifest.json")
    assert reduced["case_count"] == source_manifest["case_count"] == 91
    by_name = {case["name"]: case for case in source_manifest["cases"]}
    base = (HERE / "base.clauses").read_text(encoding="ascii").splitlines()

    total_cnf = 0
    total_lrat = 0
    max_initial = 0
    max_lrat = 0
    total_steps = 0
    total_hints = 0
    for case in reduced["cases"]:
        name = case["name"]
        source = by_name[name]
        ids_path = directory / f"{name}.ids"
        cnf_path = directory / f"{name}.cnf"
        lrat_path = directory / f"{name}.lrat"
        ids = [int(x) for x in ids_path.read_text(encoding="ascii").split()]
        assert ids == case["original_initial_ids"] == sorted(set(ids))
        assert digest(ids_path) == case["ids_sha256"]
        assert digest(cnf_path) == case["cnf_sha256"]
        assert digest(lrat_path) == case["lrat_sha256"]

        units = (HERE / "cases" / f"{name}.units").read_text(
            encoding="ascii"
        ).splitlines()
        original_clauses = [parse_clause(line) for line in base + units]
        variables, clauses = parse_cnf(cnf_path)
        assert variables == reduced["variable_count"] == 286
        assert clauses == [original_clauses[ident - 1] for ident in ids]
        assert len(clauses) == case["reduced_initial_clauses"]
        assert case["base_ids"] == sum(ident <= 16830 for ident in ids)
        assert case["unit_ids"] == sum(ident > 16830 for ident in ids)

        rows = parse_lrat(lrat_path)
        original_rows = parse_lrat(HERE / "cases" / f"{name}.lrat")
        assert [(i, c) for i, c, _ in rows] == [(i, c) for i, c, _ in original_rows]
        remap = {old: new for new, old in enumerate(ids, 1)}
        for (_, _, hints), (_, _, original_hints) in zip(rows, original_rows, strict=True):
            expected = tuple(
                remap[hint] if hint <= source["initial_clauses"] else hint
                for hint in original_hints
            )
            assert hints == expected
        steps, hints = verify_rup(clauses, rows, variables)
        total_steps += steps
        total_hints += hints
        total_cnf += cnf_path.stat().st_size
        total_lrat += lrat_path.stat().st_size
        max_initial = max(max_initial, len(clauses))
        max_lrat = max(max_lrat, lrat_path.stat().st_size)

    assert total_cnf == reduced["total_cnf_bytes"]
    assert total_lrat == reduced["total_lrat_bytes"]
    assert max_initial == reduced["max_initial_clauses"]
    assert max_lrat == reduced["max_lrat_bytes"]
    print(f"cases={len(reduced['cases'])}")
    print(f"rup_steps={total_steps}")
    print(f"rup_hints={total_hints}")
    print(f"total_cnf_bytes={total_cnf}")
    print(f"total_lrat_bytes={total_lrat}")
    print(f"max_initial_clauses={max_initial}")
    print("reduced_rup_and_mapping=ok")


if __name__ == "__main__":
    main()
