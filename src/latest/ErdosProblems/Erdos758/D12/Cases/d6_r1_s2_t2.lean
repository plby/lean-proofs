import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s2_t2_raw
  (include_str "../reduced/d6_r1_s2_t2.cnf")
  (include_str "../reduced/d6_r1_s2_t2.lrat")

def d6_r1_s2_t2_ids : String := include_str "../reduced/d6_r1_s2_t2.ids"

def d6_r1_s2_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (22, true), (23, true), (24, false), (25, false)]

private theorem d6_r1_s2_t2_sem_0_430 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 0, 430) := by
  exact d12CaseRangeProof(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 0, 430)

private theorem d6_r1_s2_t2_sem_430_861 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 430, 861) := by
  exact d12CaseRangeProof(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 430, 861)

private theorem d6_r1_s2_t2_sem_0_861 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 0, 861) := by
  intro h
  exact h.elim (d6_r1_s2_t2_sem_0_430 edge) (d6_r1_s2_t2_sem_430_861 edge)

private theorem d6_r1_s2_t2_sem_861_1292 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 861, 1292) := by
  exact d12CaseRangeProof(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 861, 1292)

private theorem d6_r1_s2_t2_sem_1292_1723 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 1292, 1723) := by
  exact d12CaseRangeProof(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 1292, 1723)

private theorem d6_r1_s2_t2_sem_861_1723 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 861, 1723) := by
  intro h
  exact h.elim (d6_r1_s2_t2_sem_861_1292 edge) (d6_r1_s2_t2_sem_1292_1723 edge)

private theorem d6_r1_s2_t2_sem_0_1723 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t2_ids, d6_r1_s2_t2_units, edge, 0, 1723) := by
  intro h
  exact h.elim (d6_r1_s2_t2_sem_0_861 edge) (d6_r1_s2_t2_sem_861_1723 edge)

theorem d6_r1_s2_t2 (edge : Nat → Prop) : D12Outcome edge d6_r1_s2_t2_units := by
  exact d6_r1_s2_t2_sem_0_1723 edge (d12CaseRaw(d6_r1_s2_t2_raw, edge))

end Erdos758.D12Certificate
