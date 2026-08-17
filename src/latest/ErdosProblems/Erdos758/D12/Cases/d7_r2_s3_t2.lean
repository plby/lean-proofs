import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s3_t2_raw
  (include_str "../reduced/d7_r2_s3_t2.cnf")
  (include_str "../reduced/d7_r2_s3_t2.lrat")

def d7_r2_s3_t2_ids : String := include_str "../reduced/d7_r2_s3_t2.ids"

def d7_r2_s3_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false), (23, true), (24, true), (25, false), (26, false)]

private theorem d7_r2_s3_t2_sem_0_459 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 0, 459) := by
  exact d12CaseRangeProof(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 0, 459)

private theorem d7_r2_s3_t2_sem_459_919 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 459, 919) := by
  exact d12CaseRangeProof(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 459, 919)

private theorem d7_r2_s3_t2_sem_0_919 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 0, 919) := by
  intro h
  exact h.elim (d7_r2_s3_t2_sem_0_459 edge) (d7_r2_s3_t2_sem_459_919 edge)

private theorem d7_r2_s3_t2_sem_919_1379 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 919, 1379) := by
  exact d12CaseRangeProof(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 919, 1379)

private theorem d7_r2_s3_t2_sem_1379_1839 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 1379, 1839) := by
  exact d12CaseRangeProof(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 1379, 1839)

private theorem d7_r2_s3_t2_sem_919_1839 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 919, 1839) := by
  intro h
  exact h.elim (d7_r2_s3_t2_sem_919_1379 edge) (d7_r2_s3_t2_sem_1379_1839 edge)

private theorem d7_r2_s3_t2_sem_0_1839 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s3_t2_ids, d7_r2_s3_t2_units, edge, 0, 1839) := by
  intro h
  exact h.elim (d7_r2_s3_t2_sem_0_919 edge) (d7_r2_s3_t2_sem_919_1839 edge)

theorem d7_r2_s3_t2 (edge : Nat → Prop) : D12Outcome edge d7_r2_s3_t2_units := by
  exact d7_r2_s3_t2_sem_0_1839 edge (d12CaseRaw(d7_r2_s3_t2_raw, edge))

end Erdos758.D12Certificate
