import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d8_r4_raw
  (include_str "../reduced/d8_r4.cnf")
  (include_str "../reduced/d8_r4.lrat")

def d8_r4_ids : String := include_str "../reduced/d8_r4.ids"

def d8_r4_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, true), (16, false), (17, false), (18, false)]

private theorem d8_r4_sem_0_16 (edge : Nat → Prop) :
    d12CaseRange(d8_r4_ids, d8_r4_units, edge, 0, 16) := by
  exact d12CaseRangeProof(d8_r4_ids, d8_r4_units, edge, 0, 16)

theorem d8_r4 (edge : Nat → Prop) : D12Outcome edge d8_r4_units := by
  exact d8_r4_sem_0_16 edge (d12CaseRaw(d8_r4_raw, edge))

end Erdos758.D12Certificate
