import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s1_t1_raw
  (include_str "../reduced/d6_r3_s1_t1.cnf")
  (include_str "../reduced/d6_r3_s1_t1.lrat")

def d6_r3_s1_t1_ids : String := include_str "../reduced/d6_r3_s1_t1.ids"

def d6_r3_s1_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (24, true), (25, false)]

private theorem d6_r3_s1_t1_sem_0_284 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 0, 284) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 0, 284)

private theorem d6_r3_s1_t1_sem_284_569 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 284, 569) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 284, 569)

private theorem d6_r3_s1_t1_sem_0_569 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 0, 569) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_0_284 edge) (d6_r3_s1_t1_sem_284_569 edge)

private theorem d6_r3_s1_t1_sem_569_853 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 569, 853) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 569, 853)

private theorem d6_r3_s1_t1_sem_853_1138 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 853, 1138) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 853, 1138)

private theorem d6_r3_s1_t1_sem_569_1138 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 569, 1138) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_569_853 edge) (d6_r3_s1_t1_sem_853_1138 edge)

private theorem d6_r3_s1_t1_sem_0_1138 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 0, 1138) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_0_569 edge) (d6_r3_s1_t1_sem_569_1138 edge)

private theorem d6_r3_s1_t1_sem_1138_1422 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1138, 1422) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1138, 1422)

private theorem d6_r3_s1_t1_sem_1422_1707 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1422, 1707) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1422, 1707)

private theorem d6_r3_s1_t1_sem_1138_1707 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1138, 1707) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_1138_1422 edge) (d6_r3_s1_t1_sem_1422_1707 edge)

private theorem d6_r3_s1_t1_sem_1707_1992 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1707, 1992) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1707, 1992)

private theorem d6_r3_s1_t1_sem_1992_2277 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1992, 2277) := by
  exact d12CaseRangeProof(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1992, 2277)

private theorem d6_r3_s1_t1_sem_1707_2277 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1707, 2277) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_1707_1992 edge) (d6_r3_s1_t1_sem_1992_2277 edge)

private theorem d6_r3_s1_t1_sem_1138_2277 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 1138, 2277) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_1138_1707 edge) (d6_r3_s1_t1_sem_1707_2277 edge)

private theorem d6_r3_s1_t1_sem_0_2277 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t1_ids, d6_r3_s1_t1_units, edge, 0, 2277) := by
  intro h
  exact h.elim (d6_r3_s1_t1_sem_0_1138 edge) (d6_r3_s1_t1_sem_1138_2277 edge)

theorem d6_r3_s1_t1 (edge : Nat → Prop) : D12Outcome edge d6_r3_s1_t1_units := by
  exact d6_r3_s1_t1_sem_0_2277 edge (d12CaseRaw(d6_r3_s1_t1_raw, edge))

end Erdos758.D12Certificate
