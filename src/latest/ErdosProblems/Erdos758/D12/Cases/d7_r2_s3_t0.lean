import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s3_t0_raw
  (include_str "../reduced/d7_r2_s3_t0.cnf")
  (include_str "../reduced/d7_r2_s3_t0.lrat")

def d7_r2_s3_t0_ids : String := include_str "../reduced/d7_r2_s3_t0.ids"

def d7_r2_s3_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false), (23, false), (24, false), (25, false), (26, false)]

private theorem d7_r2_s3_t0_sem_0_456 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t0_ids, d7_r2_s3_t0_units, edge, 0, 456) := by
  exact d12CaseRangeProof(d7_r2_s3_t0_ids, d7_r2_s3_t0_units, edge, 0, 456)

private theorem d7_r2_s3_t0_sem_456_912 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t0_ids, d7_r2_s3_t0_units, edge, 456, 912) := by
  exact d12CaseRangeProof(d7_r2_s3_t0_ids, d7_r2_s3_t0_units, edge, 456, 912)

private theorem d7_r2_s3_t0_sem_0_912 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t0_ids, d7_r2_s3_t0_units, edge, 0, 912) := by
  intro h
  exact h.elim (d7_r2_s3_t0_sem_0_456 edge) (d7_r2_s3_t0_sem_456_912 edge)

theorem d7_r2_s3_t0 (edge : Nat → Prop) : D12Outcome edge d7_r2_s3_t0_units := by
  exact d7_r2_s3_t0_sem_0_912 edge (d12CaseRaw(d7_r2_s3_t0_raw, edge))

end Erdos758.D12Certificate
