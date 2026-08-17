import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s3_t1_raw
  (include_str "../reduced/d6_r2_s3_t1.cnf")
  (include_str "../reduced/d6_r2_s3_t1.lrat")

def d6_r2_s3_t1_ids : String := include_str "../reduced/d6_r2_s3_t1.ids"

def d6_r2_s3_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (23, true), (24, false), (25, false)]

private theorem d6_r2_s3_t1_sem_0_324 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 0, 324) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 0, 324)

private theorem d6_r2_s3_t1_sem_324_649 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 324, 649) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 324, 649)

private theorem d6_r2_s3_t1_sem_0_649 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 0, 649) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_0_324 edge) (d6_r2_s3_t1_sem_324_649 edge)

private theorem d6_r2_s3_t1_sem_649_974 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 649, 974) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 649, 974)

private theorem d6_r2_s3_t1_sem_974_1299 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 974, 1299) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 974, 1299)

private theorem d6_r2_s3_t1_sem_649_1299 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 649, 1299) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_649_974 edge) (d6_r2_s3_t1_sem_974_1299 edge)

private theorem d6_r2_s3_t1_sem_0_1299 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 0, 1299) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_0_649 edge) (d6_r2_s3_t1_sem_649_1299 edge)

private theorem d6_r2_s3_t1_sem_1299_1624 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1299, 1624) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1299, 1624)

private theorem d6_r2_s3_t1_sem_1624_1949 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1624, 1949) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1624, 1949)

private theorem d6_r2_s3_t1_sem_1299_1949 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1299, 1949) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_1299_1624 edge) (d6_r2_s3_t1_sem_1624_1949 edge)

private theorem d6_r2_s3_t1_sem_1949_2274 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1949, 2274) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1949, 2274)

private theorem d6_r2_s3_t1_sem_2274_2599 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 2274, 2599) := by
  exact d12CaseRangeProof(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 2274, 2599)

private theorem d6_r2_s3_t1_sem_1949_2599 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1949, 2599) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_1949_2274 edge) (d6_r2_s3_t1_sem_2274_2599 edge)

private theorem d6_r2_s3_t1_sem_1299_2599 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 1299, 2599) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_1299_1949 edge) (d6_r2_s3_t1_sem_1949_2599 edge)

private theorem d6_r2_s3_t1_sem_0_2599 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t1_ids, d6_r2_s3_t1_units, edge, 0, 2599) := by
  intro h
  exact h.elim (d6_r2_s3_t1_sem_0_1299 edge) (d6_r2_s3_t1_sem_1299_2599 edge)

theorem d6_r2_s3_t1 (edge : Nat → Prop) : D12Outcome edge d6_r2_s3_t1_units := by
  exact d6_r2_s3_t1_sem_0_2599 edge (d12CaseRaw(d6_r2_s3_t1_raw, edge))

end Erdos758.D12Certificate
