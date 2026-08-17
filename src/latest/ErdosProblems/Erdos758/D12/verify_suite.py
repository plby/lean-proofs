#!/usr/bin/env python3
"""Check D12 suite structure, hashes, and the RUP-only LRAT discipline."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_lrat(path: Path, initial: int):
    known = set(range(1, initial + 1))
    additions = 0
    final_empty = None
    with path.open(encoding="ascii") as stream:
        for line in stream:
            fields = line.split()
            assert fields
            ident = int(fields[0])
            assert fields[1] != "d"
            numbers = [int(x) for x in fields[1:]]
            split = numbers.index(0)
            clause = numbers[:split]
            hints = numbers[split + 1:-1]
            assert numbers[-1] == 0
            assert hints
            assert all(hint > 0 for hint in hints)
            assert all(hint in known for hint in hints)
            assert ident not in known
            known.add(ident)
            additions += 1
            if not clause:
                final_empty = ident
    assert final_empty is not None
    return additions, final_empty


def main() -> None:
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="ascii"))
    assert manifest["variable_count"] == 286
    assert manifest["base_clause_count"] == 16830
    assert manifest["case_count"] == 91
    assert len(manifest["cases"]) == 91
    base = (HERE / "base.clauses").read_bytes()
    assert digest_bytes(base) == manifest["base_sha256"]

    names = set()
    total = 0
    maximum = 0
    for case in manifest["cases"]:
        name = case["name"]
        assert name not in names
        names.add(name)
        assert case["initial_clauses"] == 16830 + len(case["assumptions"])
        units = HERE / "cases" / f"{name}.units"
        proof = HERE / "cases" / f"{name}.lrat"
        assert digest(units) == case["units_sha256"]
        assert digest(proof) == case["lrat_sha256"]
        header = f"p cnf 286 {case['initial_clauses']}\n".encode("ascii")
        assert digest_bytes(header + base + units.read_bytes()) == case["cnf_sha256"]
        assert proof.stat().st_size == case["lrat_bytes"]
        check_lrat(proof, case["initial_clauses"])
        total += proof.stat().st_size
        maximum = max(maximum, proof.stat().st_size)
    assert total == manifest["total_lrat_bytes"]
    assert maximum == manifest["max_lrat_bytes"]

    expected = {}
    with (HERE / "SHA256SUMS").open(encoding="ascii") as stream:
        for line in stream:
            value, rel = line.rstrip().split("  ", 1)
            expected[rel] = value
    for rel, value in expected.items():
        assert digest(HERE / rel) == value
    print(f"cases={len(names)}")
    print(f"total_lrat_bytes={total}")
    print(f"max_lrat_bytes={maximum}")
    print("rup_only=yes")
    print("hashes=ok")


if __name__ == "__main__":
    main()
