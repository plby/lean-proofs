#!/usr/bin/env python3
"""Dependency-trim a text LRAT proof containing only RUP additions."""

import sys

source, target, initial_text = sys.argv[1:]
initial = int(initial_text)
adds = []
by_id = {}
final_empty = None

with open(source, encoding="ascii") as f:
    for line in f:
        fields = line.split()
        if not fields:
            continue
        ident = int(fields[0])
        if len(fields) > 1 and fields[1] == "d":
            continue
        nums = [int(x) for x in fields[1:]]
        split = nums.index(0)
        clause = nums[:split]
        hints_with_zero = nums[split + 1:]
        assert hints_with_zero and hints_with_zero[-1] == 0
        hints = hints_with_zero[:-1]
        assert all(h > 0 for h in hints), "RAT hint encountered"
        row = (ident, clause, hints, line)
        adds.append(row)
        by_id[ident] = row
        if not clause:
            final_empty = ident

assert final_empty is not None
needed = {final_empty}
work = [final_empty]
while work:
    ident = work.pop()
    for hint in by_id[ident][2]:
        if hint > initial and hint not in needed:
            assert hint in by_id, (ident, hint)
            needed.add(hint)
            work.append(hint)

with open(target, "w", encoding="ascii") as f:
    for ident, _clause, _hints, line in adds:
        if ident in needed:
            f.write(line)

print(f"input_additions={len(adds)}")
print(f"kept_additions={len(needed)}")
print(f"final_empty={final_empty}")
