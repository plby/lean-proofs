import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r1_s2_raw
  (include_str "../reduced/d7_r1_s2.cnf")
  (include_str "../reduced/d7_r1_s2.lrat")

def d7_r1_s2_ids : String := include_str "../reduced/d7_r1_s2.ids"

def d7_r1_s2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, false), (21, false)]

private theorem d7_r1_s2_sem_0_328 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 0, 328) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 0, 328)

private theorem d7_r1_s2_sem_328_656 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 328, 656) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 328, 656)

private theorem d7_r1_s2_sem_0_656 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 0, 656) := by
  intro h
  exact h.elim (d7_r1_s2_sem_0_328 edge) (d7_r1_s2_sem_328_656 edge)

private theorem d7_r1_s2_sem_656_984 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 656, 984) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 656, 984)

private theorem d7_r1_s2_sem_984_1313 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 984, 1313) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 984, 1313)

private theorem d7_r1_s2_sem_656_1313 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 656, 1313) := by
  intro h
  exact h.elim (d7_r1_s2_sem_656_984 edge) (d7_r1_s2_sem_984_1313 edge)

private theorem d7_r1_s2_sem_0_1313 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 0, 1313) := by
  intro h
  exact h.elim (d7_r1_s2_sem_0_656 edge) (d7_r1_s2_sem_656_1313 edge)

private theorem d7_r1_s2_sem_1313_1641 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1313, 1641) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 1313, 1641)

private theorem d7_r1_s2_sem_1641_1970 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1641, 1970) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 1641, 1970)

private theorem d7_r1_s2_sem_1313_1970 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1313, 1970) := by
  intro h
  exact h.elim (d7_r1_s2_sem_1313_1641 edge) (d7_r1_s2_sem_1641_1970 edge)

private theorem d7_r1_s2_sem_1970_2298 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1970, 2298) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 1970, 2298)

private theorem d7_r1_s2_sem_2298_2627 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 2298, 2627) := by
  exact d12CaseRangeProof(d7_r1_s2_ids, d7_r1_s2_units, edge, 2298, 2627)

private theorem d7_r1_s2_sem_1970_2627 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1970, 2627) := by
  intro h
  exact h.elim (d7_r1_s2_sem_1970_2298 edge) (d7_r1_s2_sem_2298_2627 edge)

private theorem d7_r1_s2_sem_1313_2627 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 1313, 2627) := by
  intro h
  exact h.elim (d7_r1_s2_sem_1313_1970 edge) (d7_r1_s2_sem_1970_2627 edge)

private theorem d7_r1_s2_sem_0_2627 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s2_ids, d7_r1_s2_units, edge, 0, 2627) := by
  intro h
  exact h.elim (d7_r1_s2_sem_0_1313 edge) (d7_r1_s2_sem_1313_2627 edge)

theorem d7_r1_s2 (edge : Nat → Prop) : D12Outcome edge d7_r1_s2_units := by
  exact d7_r1_s2_sem_0_2627 edge (d12CaseRaw(d7_r1_s2_raw, edge))

end Erdos758.D12Certificate
