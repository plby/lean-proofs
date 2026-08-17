import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s3_t3_raw
  (include_str "../reduced/d7_r2_s3_t3.cnf")
  (include_str "../reduced/d7_r2_s3_t3.lrat")

def d7_r2_s3_t3_ids : String := include_str "../reduced/d7_r2_s3_t3.ids"

def d7_r2_s3_t3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false), (23, true), (24, true), (25, true), (26, false)]

private theorem d7_r2_s3_t3_sem_0_14 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t3_ids, d7_r2_s3_t3_units, edge, 0, 14) := by
  exact d12CaseRangeProof(d7_r2_s3_t3_ids, d7_r2_s3_t3_units, edge, 0, 14)

theorem d7_r2_s3_t3 (edge : Nat → Prop) : D12Outcome edge d7_r2_s3_t3_units := by
  exact d7_r2_s3_t3_sem_0_14 edge (d12CaseRaw(d7_r2_s3_t3_raw, edge))

end Erdos758.D12Certificate
