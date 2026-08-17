#!/usr/bin/env python3
"""Generate D8.cnf; see README.md for the variable and clause map."""

from itertools import combinations
from pathlib import Path

N = 8
edges = list(combinations(range(N), 2))
triangles = list(combinations(range(N), 3))
edge_var = {e: i + 1 for i, e in enumerate(edges)}
hom_var = {t: len(edges) + i + 1 for i, t in enumerate(triangles)}
clauses = []

for q in combinations(range(N), 4):
    qe = [edge_var[e] for e in combinations(q, 2)]
    clauses.append(tuple(-x for x in qe))
    clauses.append(tuple(qe))

for t in triangles:
    a, b, c = t
    x, y, z = edge_var[(a, b)], edge_var[(a, c)], edge_var[(b, c)]
    h = hom_var[t]
    clauses.append((h, -x, -y, -z))
    clauses.append((h, x, y, z))

disjoint_pairs = []
for i, s in enumerate(triangles):
    ss = set(s)
    for t in triangles[i + 1:]:
        if ss.isdisjoint(t):
            disjoint_pairs.append((s, t))
            clauses.append((-hom_var[s], -hom_var[t]))

assert len(edges) == 28
assert len(triangles) == 56
assert len(disjoint_pairs) == 280
assert len(clauses) == 532

out = Path(__file__).with_name("D8.cnf")
with out.open("w", encoding="ascii") as f:
    f.write(f"p cnf 84 {len(clauses)}\n")
    for clause in clauses:
        f.write(" ".join(map(str, clause)) + " 0\n")

