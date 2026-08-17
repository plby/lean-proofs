import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s2_t1_raw
  (include_str "../reduced/d6_r2_s2_t1.cnf")
  (include_str "../reduced/d6_r2_s2_t1.lrat")

def d6_r2_s2_t1_ids : String := include_str "../reduced/d6_r2_s2_t1.ids"

def d6_r2_s2_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (23, true), (24, false), (25, false)]

private theorem d6_r2_s2_t1_sem_0_342 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 342) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 342)

private theorem d6_r2_s2_t1_sem_342_684 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 342, 684) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 342, 684)

private theorem d6_r2_s2_t1_sem_0_684 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 684) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_0_342 edge) (d6_r2_s2_t1_sem_342_684 edge)

private theorem d6_r2_s2_t1_sem_684_1026 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 684, 1026) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 684, 1026)

private theorem d6_r2_s2_t1_sem_1026_1369 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1026, 1369) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1026, 1369)

private theorem d6_r2_s2_t1_sem_684_1369 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 684, 1369) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_684_1026 edge) (d6_r2_s2_t1_sem_1026_1369 edge)

private theorem d6_r2_s2_t1_sem_0_1369 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 1369) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_0_684 edge) (d6_r2_s2_t1_sem_684_1369 edge)

private theorem d6_r2_s2_t1_sem_1369_1711 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1369, 1711) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1369, 1711)

private theorem d6_r2_s2_t1_sem_1711_2054 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1711, 2054) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1711, 2054)

private theorem d6_r2_s2_t1_sem_1369_2054 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1369, 2054) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_1369_1711 edge) (d6_r2_s2_t1_sem_1711_2054 edge)

private theorem d6_r2_s2_t1_sem_2054_2396 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 2054, 2396) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 2054, 2396)

private theorem d6_r2_s2_t1_sem_2396_2739 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 2396, 2739) := by
  exact d12CaseRangeProof(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 2396, 2739)

private theorem d6_r2_s2_t1_sem_2054_2739 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 2054, 2739) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_2054_2396 edge) (d6_r2_s2_t1_sem_2396_2739 edge)

private theorem d6_r2_s2_t1_sem_1369_2739 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 1369, 2739) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_1369_2054 edge) (d6_r2_s2_t1_sem_2054_2739 edge)

private theorem d6_r2_s2_t1_sem_0_2739 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t1_ids, d6_r2_s2_t1_units, edge, 0, 2739) := by
  intro h
  exact h.elim (d6_r2_s2_t1_sem_0_1369 edge) (d6_r2_s2_t1_sem_1369_2739 edge)

theorem d6_r2_s2_t1 (edge : Nat → Prop) : D12Outcome edge d6_r2_s2_t1_units := by
  exact d6_r2_s2_t1_sem_0_2739 edge (d12CaseRaw(d6_r2_s2_t1_raw, edge))

end Erdos758.D12Certificate
