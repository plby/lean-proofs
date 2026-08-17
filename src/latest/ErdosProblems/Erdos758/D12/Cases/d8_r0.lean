import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d8_r0_raw
  (include_str "../reduced/d8_r0.cnf")
  (include_str "../reduced/d8_r0.lrat")

def d8_r0_ids : String := include_str "../reduced/d8_r0.ids"

def d8_r0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, false), (18, false)]

private theorem d8_r0_sem_0_58 (edge : Nat → Prop) :
    d12CaseRange(d8_r0_ids, d8_r0_units, edge, 0, 58) := by
  exact d12CaseRangeProof(d8_r0_ids, d8_r0_units, edge, 0, 58)

theorem d8_r0 (edge : Nat → Prop) : D12Outcome edge d8_r0_units := by
  exact d8_r0_sem_0_58 edge (d12CaseRaw(d8_r0_raw, edge))

end Erdos758.D12Certificate
