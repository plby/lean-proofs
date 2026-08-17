import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r0_raw
  (include_str "../reduced/d7_r0.cnf")
  (include_str "../reduced/d7_r0.lrat")

def d7_r0_ids : String := include_str "../reduced/d7_r0.ids"

def d7_r0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, false)]

private theorem d7_r0_sem_0_52 (edge : Nat → Prop) :
    d12CaseRange(d7_r0_ids, d7_r0_units, edge, 0, 52) := by
  exact d12CaseRangeProof(d7_r0_ids, d7_r0_units, edge, 0, 52)

theorem d7_r0 (edge : Nat → Prop) : D12Outcome edge d7_r0_units := by
  exact d7_r0_sem_0_52 edge (d12CaseRaw(d7_r0_raw, edge))

end Erdos758.D12Certificate
