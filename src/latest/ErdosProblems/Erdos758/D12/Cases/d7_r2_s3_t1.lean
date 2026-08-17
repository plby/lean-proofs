import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s3_t1_raw
  (include_str "../reduced/d7_r2_s3_t1.cnf")
  (include_str "../reduced/d7_r2_s3_t1.lrat")

def d7_r2_s3_t1_ids : String := include_str "../reduced/d7_r2_s3_t1.ids"

def d7_r2_s3_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false), (23, true), (24, false), (25, false), (26, false)]

private theorem d7_r2_s3_t1_sem_0_472 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 0, 472) := by
  exact d12CaseRangeProof(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 0, 472)

private theorem d7_r2_s3_t1_sem_472_944 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 472, 944) := by
  exact d12CaseRangeProof(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 472, 944)

private theorem d7_r2_s3_t1_sem_0_944 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 0, 944) := by
  intro h
  exact h.elim (d7_r2_s3_t1_sem_0_472 edge) (d7_r2_s3_t1_sem_472_944 edge)

private theorem d7_r2_s3_t1_sem_944_1416 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 944, 1416) := by
  exact d12CaseRangeProof(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 944, 1416)

private theorem d7_r2_s3_t1_sem_1416_1888 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 1416, 1888) := by
  exact d12CaseRangeProof(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 1416, 1888)

private theorem d7_r2_s3_t1_sem_944_1888 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 944, 1888) := by
  intro h
  exact h.elim (d7_r2_s3_t1_sem_944_1416 edge) (d7_r2_s3_t1_sem_1416_1888 edge)

private theorem d7_r2_s3_t1_sem_0_1888 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t1_ids, d7_r2_s3_t1_units, edge, 0, 1888) := by
  intro h
  exact h.elim (d7_r2_s3_t1_sem_0_944 edge) (d7_r2_s3_t1_sem_944_1888 edge)

theorem d7_r2_s3_t1 (edge : Nat → Prop) : D12Outcome edge d7_r2_s3_t1_units := by
  exact d7_r2_s3_t1_sem_0_1888 edge (d12CaseRaw(d7_r2_s3_t1_raw, edge))

end Erdos758.D12Certificate
