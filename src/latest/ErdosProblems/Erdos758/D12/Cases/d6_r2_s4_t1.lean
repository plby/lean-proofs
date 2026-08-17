import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s4_t1_raw
  (include_str "../reduced/d6_r2_s4_t1.cnf")
  (include_str "../reduced/d6_r2_s4_t1.lrat")

def d6_r2_s4_t1_ids : String := include_str "../reduced/d6_r2_s4_t1.ids"

def d6_r2_s4_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (23, true), (24, false), (25, false)]

private theorem d6_r2_s4_t1_sem_0_293 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 0, 293) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 0, 293)

private theorem d6_r2_s4_t1_sem_293_586 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 293, 586) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 293, 586)

private theorem d6_r2_s4_t1_sem_0_586 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 0, 586) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_0_293 edge) (d6_r2_s4_t1_sem_293_586 edge)

private theorem d6_r2_s4_t1_sem_586_879 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 586, 879) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 586, 879)

private theorem d6_r2_s4_t1_sem_879_1172 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 879, 1172) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 879, 1172)

private theorem d6_r2_s4_t1_sem_586_1172 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 586, 1172) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_586_879 edge) (d6_r2_s4_t1_sem_879_1172 edge)

private theorem d6_r2_s4_t1_sem_0_1172 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 0, 1172) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_0_586 edge) (d6_r2_s4_t1_sem_586_1172 edge)

private theorem d6_r2_s4_t1_sem_1172_1465 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1172, 1465) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1172, 1465)

private theorem d6_r2_s4_t1_sem_1465_1758 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1465, 1758) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1465, 1758)

private theorem d6_r2_s4_t1_sem_1172_1758 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1172, 1758) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_1172_1465 edge) (d6_r2_s4_t1_sem_1465_1758 edge)

private theorem d6_r2_s4_t1_sem_1758_2051 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1758, 2051) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1758, 2051)

private theorem d6_r2_s4_t1_sem_2051_2344 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 2051, 2344) := by
  exact d12CaseRangeProof(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 2051, 2344)

private theorem d6_r2_s4_t1_sem_1758_2344 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1758, 2344) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_1758_2051 edge) (d6_r2_s4_t1_sem_2051_2344 edge)

private theorem d6_r2_s4_t1_sem_1172_2344 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 1172, 2344) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_1172_1758 edge) (d6_r2_s4_t1_sem_1758_2344 edge)

private theorem d6_r2_s4_t1_sem_0_2344 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t1_ids, d6_r2_s4_t1_units, edge, 0, 2344) := by
  intro h
  exact h.elim (d6_r2_s4_t1_sem_0_1172 edge) (d6_r2_s4_t1_sem_1172_2344 edge)

theorem d6_r2_s4_t1 (edge : Nat → Prop) : D12Outcome edge d6_r2_s4_t1_units := by
  exact d6_r2_s4_t1_sem_0_2344 edge (d12CaseRaw(d6_r2_s4_t1_raw, edge))

end Erdos758.D12Certificate
