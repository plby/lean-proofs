import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r3_s4_raw
  (include_str "../reduced/d7_r3_s4.cnf")
  (include_str "../reduced/d7_r3_s4.lrat")

def d7_r3_s4_ids : String := include_str "../reduced/d7_r3_s4.ids"

def d7_r3_s4_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, true)]

private theorem d7_r3_s4_sem_0_411 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s4_ids, d7_r3_s4_units, edge, 0, 411) := by
  exact d12CaseRangeProof(d7_r3_s4_ids, d7_r3_s4_units, edge, 0, 411)

private theorem d7_r3_s4_sem_411_822 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s4_ids, d7_r3_s4_units, edge, 411, 822) := by
  exact d12CaseRangeProof(d7_r3_s4_ids, d7_r3_s4_units, edge, 411, 822)

private theorem d7_r3_s4_sem_0_822 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s4_ids, d7_r3_s4_units, edge, 0, 822) := by
  intro h
  exact h.elim (d7_r3_s4_sem_0_411 edge) (d7_r3_s4_sem_411_822 edge)

theorem d7_r3_s4 (edge : Nat → Prop) : D12Outcome edge d7_r3_s4_units := by
  exact d7_r3_s4_sem_0_822 edge (d12CaseRaw(d7_r3_s4_raw, edge))

end Erdos758.D12Certificate
