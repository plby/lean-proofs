import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s4_raw
  (include_str "../reduced/d6_r0_s4.cnf")
  (include_str "../reduced/d6_r0_s4.lrat")

def d6_r0_s4_ids : String := include_str "../reduced/d6_r0_s4.ids"

def d6_r0_s4_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false)]

private theorem d6_r0_s4_sem_0_505 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 0, 505) := by
  exact d12CaseRangeProof(d6_r0_s4_ids, d6_r0_s4_units, edge, 0, 505)

private theorem d6_r0_s4_sem_505_1011 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 505, 1011) := by
  exact d12CaseRangeProof(d6_r0_s4_ids, d6_r0_s4_units, edge, 505, 1011)

private theorem d6_r0_s4_sem_0_1011 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 0, 1011) := by
  intro h
  exact h.elim (d6_r0_s4_sem_0_505 edge) (d6_r0_s4_sem_505_1011 edge)

private theorem d6_r0_s4_sem_1011_1516 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 1011, 1516) := by
  exact d12CaseRangeProof(d6_r0_s4_ids, d6_r0_s4_units, edge, 1011, 1516)

private theorem d6_r0_s4_sem_1516_2022 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 1516, 2022) := by
  exact d12CaseRangeProof(d6_r0_s4_ids, d6_r0_s4_units, edge, 1516, 2022)

private theorem d6_r0_s4_sem_1011_2022 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 1011, 2022) := by
  intro h
  exact h.elim (d6_r0_s4_sem_1011_1516 edge) (d6_r0_s4_sem_1516_2022 edge)

private theorem d6_r0_s4_sem_0_2022 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s4_ids, d6_r0_s4_units, edge, 0, 2022) := by
  intro h
  exact h.elim (d6_r0_s4_sem_0_1011 edge) (d6_r0_s4_sem_1011_2022 edge)

theorem d6_r0_s4 (edge : Nat → Prop) : D12Outcome edge d6_r0_s4_units := by
  exact d6_r0_s4_sem_0_2022 edge (d12CaseRaw(d6_r0_s4_raw, edge))

end Erdos758.D12Certificate
