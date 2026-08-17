import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s1_raw
  (include_str "../reduced/d6_r0_s1.cnf")
  (include_str "../reduced/d6_r0_s1.lrat")

def d6_r0_s1_ids : String := include_str "../reduced/d6_r0_s1.ids"

def d6_r0_s1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r0_s1_sem_0_361 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 0, 361) := by
  exact d12CaseRangeProof(d6_r0_s1_ids, d6_r0_s1_units, edge, 0, 361)

private theorem d6_r0_s1_sem_361_722 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 361, 722) := by
  exact d12CaseRangeProof(d6_r0_s1_ids, d6_r0_s1_units, edge, 361, 722)

private theorem d6_r0_s1_sem_0_722 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 0, 722) := by
  intro h
  exact h.elim (d6_r0_s1_sem_0_361 edge) (d6_r0_s1_sem_361_722 edge)

private theorem d6_r0_s1_sem_722_1083 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 722, 1083) := by
  exact d12CaseRangeProof(d6_r0_s1_ids, d6_r0_s1_units, edge, 722, 1083)

private theorem d6_r0_s1_sem_1083_1445 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 1083, 1445) := by
  exact d12CaseRangeProof(d6_r0_s1_ids, d6_r0_s1_units, edge, 1083, 1445)

private theorem d6_r0_s1_sem_722_1445 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 722, 1445) := by
  intro h
  exact h.elim (d6_r0_s1_sem_722_1083 edge) (d6_r0_s1_sem_1083_1445 edge)

private theorem d6_r0_s1_sem_0_1445 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s1_ids, d6_r0_s1_units, edge, 0, 1445) := by
  intro h
  exact h.elim (d6_r0_s1_sem_0_722 edge) (d6_r0_s1_sem_722_1445 edge)

theorem d6_r0_s1 (edge : Nat → Prop) : D12Outcome edge d6_r0_s1_units := by
  exact d6_r0_s1_sem_0_1445 edge (d12CaseRaw(d6_r0_s1_raw, edge))

end Erdos758.D12Certificate
