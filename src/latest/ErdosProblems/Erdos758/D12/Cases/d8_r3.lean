import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d8_r3_raw
  (include_str "../reduced/d8_r3.cnf")
  (include_str "../reduced/d8_r3.lrat")

def d8_r3_ids : String := include_str "../reduced/d8_r3.ids"

def d8_r3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, false)]

private theorem d8_r3_sem_0_304 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 0, 304) := by
  exact d12CaseRangeProof(d8_r3_ids, d8_r3_units, edge, 0, 304)

private theorem d8_r3_sem_304_608 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 304, 608) := by
  exact d12CaseRangeProof(d8_r3_ids, d8_r3_units, edge, 304, 608)

private theorem d8_r3_sem_0_608 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 0, 608) := by
  intro h
  exact h.elim (d8_r3_sem_0_304 edge) (d8_r3_sem_304_608 edge)

private theorem d8_r3_sem_608_912 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 608, 912) := by
  exact d12CaseRangeProof(d8_r3_ids, d8_r3_units, edge, 608, 912)

private theorem d8_r3_sem_912_1217 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 912, 1217) := by
  exact d12CaseRangeProof(d8_r3_ids, d8_r3_units, edge, 912, 1217)

private theorem d8_r3_sem_608_1217 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 608, 1217) := by
  intro h
  exact h.elim (d8_r3_sem_608_912 edge) (d8_r3_sem_912_1217 edge)

private theorem d8_r3_sem_0_1217 (edge : Nat → Prop) :
    d12CaseRange(d8_r3_ids, d8_r3_units, edge, 0, 1217) := by
  intro h
  exact h.elim (d8_r3_sem_0_608 edge) (d8_r3_sem_608_1217 edge)

theorem d8_r3 (edge : Nat → Prop) : D12Outcome edge d8_r3_units := by
  exact d8_r3_sem_0_1217 edge (d12CaseRaw(d8_r3_raw, edge))

end Erdos758.D12Certificate
