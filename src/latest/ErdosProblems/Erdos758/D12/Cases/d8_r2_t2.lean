import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d8_r2_t2_raw
  (include_str "../reduced/d8_r2_t2.cnf")
  (include_str "../reduced/d8_r2_t2.lrat")

def d8_r2_t2_ids : String := include_str "../reduced/d8_r2_t2.ids"

def d8_r2_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, false), (23, true), (24, true), (25, false), (26, false), (27, false)]

private theorem d8_r2_t2_sem_0_318 (edge : Nat → Prop) :
    d12CaseRange(d8_r2_t2_ids, d8_r2_t2_units, edge, 0, 318) := by
  exact d12CaseRangeProof(d8_r2_t2_ids, d8_r2_t2_units, edge, 0, 318)

theorem d8_r2_t2 (edge : Nat → Prop) : D12Outcome edge d8_r2_t2_units := by
  exact d8_r2_t2_sem_0_318 edge (d12CaseRaw(d8_r2_t2_raw, edge))

end Erdos758.D12Certificate
