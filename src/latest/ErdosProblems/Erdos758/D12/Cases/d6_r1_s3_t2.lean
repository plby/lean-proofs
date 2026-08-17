import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s3_t2_raw
  (include_str "../reduced/d6_r1_s3_t2.cnf")
  (include_str "../reduced/d6_r1_s3_t2.lrat")

def d6_r1_s3_t2_ids : String := include_str "../reduced/d6_r1_s3_t2.ids"

def d6_r1_s3_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (22, true), (23, true), (24, false), (25, false)]

private theorem d6_r1_s3_t2_sem_0_512 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 0, 512) := by
  exact d12CaseRangeProof(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 0, 512)

private theorem d6_r1_s3_t2_sem_512_1024 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 512, 1024) := by
  exact d12CaseRangeProof(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 512, 1024)

private theorem d6_r1_s3_t2_sem_0_1024 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 0, 1024) := by
  intro h
  exact h.elim (d6_r1_s3_t2_sem_0_512 edge) (d6_r1_s3_t2_sem_512_1024 edge)

private theorem d6_r1_s3_t2_sem_1024_1536 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1024, 1536) := by
  exact d12CaseRangeProof(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1024, 1536)

private theorem d6_r1_s3_t2_sem_1536_1792 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1536, 1792) := by
  exact d12CaseRangeProof(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1536, 1792)

private theorem d6_r1_s3_t2_sem_1792_2049 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1792, 2049) := by
  exact d12CaseRangeProof(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1792, 2049)

private theorem d6_r1_s3_t2_sem_1536_2049 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1536, 2049) := by
  intro h
  exact h.elim (d6_r1_s3_t2_sem_1536_1792 edge) (d6_r1_s3_t2_sem_1792_2049 edge)

private theorem d6_r1_s3_t2_sem_1024_2049 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 1024, 2049) := by
  intro h
  exact h.elim (d6_r1_s3_t2_sem_1024_1536 edge) (d6_r1_s3_t2_sem_1536_2049 edge)

private theorem d6_r1_s3_t2_sem_0_2049 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t2_ids, d6_r1_s3_t2_units, edge, 0, 2049) := by
  intro h
  exact h.elim (d6_r1_s3_t2_sem_0_1024 edge) (d6_r1_s3_t2_sem_1024_2049 edge)

theorem d6_r1_s3_t2 (edge : Nat → Prop) : D12Outcome edge d6_r1_s3_t2_units := by
  exact d6_r1_s3_t2_sem_0_2049 edge (d12CaseRaw(d6_r1_s3_t2_raw, edge))

end Erdos758.D12Certificate
