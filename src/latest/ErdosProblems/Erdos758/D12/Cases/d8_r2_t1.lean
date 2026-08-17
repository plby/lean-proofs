import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d8_r2_t1_raw
  (include_str "../reduced/d8_r2_t1.cnf")
  (include_str "../reduced/d8_r2_t1.lrat")

def d8_r2_t1_ids : String := include_str "../reduced/d8_r2_t1.ids"

def d8_r2_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, false), (23, true), (24, false), (25, false), (26, false), (27, false)]

private theorem d8_r2_t1_sem_0_374 (edge : Nat → Prop) :
    d12CaseRange(d8_r2_t1_ids, d8_r2_t1_units, edge, 0, 374) := by
  exact d12CaseRangeProof(d8_r2_t1_ids, d8_r2_t1_units, edge, 0, 374)

theorem d8_r2_t1 (edge : Nat → Prop) : D12Outcome edge d8_r2_t1_units := by
  exact d8_r2_t1_sem_0_374 edge (d12CaseRaw(d8_r2_t1_raw, edge))

end Erdos758.D12Certificate
