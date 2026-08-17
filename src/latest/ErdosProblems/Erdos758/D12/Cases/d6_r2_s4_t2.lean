import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s4_t2_raw
  (include_str "../reduced/d6_r2_s4_t2.cnf")
  (include_str "../reduced/d6_r2_s4_t2.lrat")

def d6_r2_s4_t2_ids : String := include_str "../reduced/d6_r2_s4_t2.ids"

def d6_r2_s4_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (23, true), (24, true), (25, false)]

private theorem d6_r2_s4_t2_sem_0_468 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 0, 468) := by
  exact d12CaseRangeProof(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 0, 468)

private theorem d6_r2_s4_t2_sem_468_936 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 468, 936) := by
  exact d12CaseRangeProof(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 468, 936)

private theorem d6_r2_s4_t2_sem_0_936 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 0, 936) := by
  intro h
  exact h.elim (d6_r2_s4_t2_sem_0_468 edge) (d6_r2_s4_t2_sem_468_936 edge)

private theorem d6_r2_s4_t2_sem_936_1404 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 936, 1404) := by
  exact d12CaseRangeProof(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 936, 1404)

private theorem d6_r2_s4_t2_sem_1404_1873 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 1404, 1873) := by
  exact d12CaseRangeProof(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 1404, 1873)

private theorem d6_r2_s4_t2_sem_936_1873 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 936, 1873) := by
  intro h
  exact h.elim (d6_r2_s4_t2_sem_936_1404 edge) (d6_r2_s4_t2_sem_1404_1873 edge)

private theorem d6_r2_s4_t2_sem_0_1873 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t2_ids, d6_r2_s4_t2_units, edge, 0, 1873) := by
  intro h
  exact h.elim (d6_r2_s4_t2_sem_0_936 edge) (d6_r2_s4_t2_sem_936_1873 edge)

theorem d6_r2_s4_t2 (edge : Nat → Prop) : D12Outcome edge d6_r2_s4_t2_units := by
  exact d6_r2_s4_t2_sem_0_1873 edge (d12CaseRaw(d6_r2_s4_t2_raw, edge))

end Erdos758.D12Certificate
