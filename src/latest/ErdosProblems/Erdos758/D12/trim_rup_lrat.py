#!/usr/bin/env python3
"""Retain the dependency cone of the final empty clause in a RUP LRAT."""

from __future__ import annotations

import argparse
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    parser.add_argument("initial_clauses", type=int)
    args = parser.parse_args()

    additions = []
    by_id = {}
    final_empty = None
    with args.source.open(encoding="ascii") as stream:
        for line in stream:
            fields = line.split()
            if not fields:
                continue
            ident = int(fields[0])
            if len(fields) > 1 and fields[1] == "d":
                continue
            numbers = [int(x) for x in fields[1:]]
            split = numbers.index(0)
            clause = numbers[:split]
            hints = numbers[split + 1:-1]
            assert numbers[-1] == 0
            assert all(hint > 0 for hint in hints)
            row = ident, clause, hints, line
            additions.append(row)
            by_id[ident] = row
            if not clause:
                final_empty = ident
    assert final_empty is not None

    needed = {final_empty}
    work = [final_empty]
    while work:
        ident = work.pop()
        for hint in by_id[ident][2]:
            if hint > args.initial_clauses and hint not in needed:
                assert hint in by_id
                needed.add(hint)
                work.append(hint)

    with args.target.open("w", encoding="ascii", newline="\n") as stream:
        for ident, _clause, _hints, line in additions:
            if ident in needed:
                stream.write(line)
    print(f"input_additions={len(additions)}")
    print(f"kept_additions={len(needed)}")
    print(f"final_empty={final_empty}")


if __name__ == "__main__":
    main()
