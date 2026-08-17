import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s3_raw
  (include_str "../reduced/d6_r0_s3.cnf")
  (include_str "../reduced/d6_r0_s3.lrat")

def d6_r0_s3_ids : String := include_str "../reduced/d6_r0_s3.ids"

def d6_r0_s3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false)]

private theorem d6_r0_s3_sem_0_329 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 0, 329) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 0, 329)

private theorem d6_r0_s3_sem_329_658 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 329, 658) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 329, 658)

private theorem d6_r0_s3_sem_0_658 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 0, 658) := by
  intro h
  exact h.elim (d6_r0_s3_sem_0_329 edge) (d6_r0_s3_sem_329_658 edge)

private theorem d6_r0_s3_sem_658_987 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 658, 987) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 658, 987)

private theorem d6_r0_s3_sem_987_1316 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 987, 1316) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 987, 1316)

private theorem d6_r0_s3_sem_658_1316 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 658, 1316) := by
  intro h
  exact h.elim (d6_r0_s3_sem_658_987 edge) (d6_r0_s3_sem_987_1316 edge)

private theorem d6_r0_s3_sem_0_1316 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 0, 1316) := by
  intro h
  exact h.elim (d6_r0_s3_sem_0_658 edge) (d6_r0_s3_sem_658_1316 edge)

private theorem d6_r0_s3_sem_1316_1645 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1316, 1645) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 1316, 1645)

private theorem d6_r0_s3_sem_1645_1974 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1645, 1974) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 1645, 1974)

private theorem d6_r0_s3_sem_1316_1974 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1316, 1974) := by
  intro h
  exact h.elim (d6_r0_s3_sem_1316_1645 edge) (d6_r0_s3_sem_1645_1974 edge)

private theorem d6_r0_s3_sem_1974_2303 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1974, 2303) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 1974, 2303)

private theorem d6_r0_s3_sem_2303_2633 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 2303, 2633) := by
  exact d12CaseRangeProof(d6_r0_s3_ids, d6_r0_s3_units, edge, 2303, 2633)

private theorem d6_r0_s3_sem_1974_2633 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1974, 2633) := by
  intro h
  exact h.elim (d6_r0_s3_sem_1974_2303 edge) (d6_r0_s3_sem_2303_2633 edge)

private theorem d6_r0_s3_sem_1316_2633 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 1316, 2633) := by
  intro h
  exact h.elim (d6_r0_s3_sem_1316_1974 edge) (d6_r0_s3_sem_1974_2633 edge)

private theorem d6_r0_s3_sem_0_2633 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s3_ids, d6_r0_s3_units, edge, 0, 2633) := by
  intro h
  exact h.elim (d6_r0_s3_sem_0_1316 edge) (d6_r0_s3_sem_1316_2633 edge)

theorem d6_r0_s3 (edge : Nat → Prop) : D12Outcome edge d6_r0_s3_units := by
  exact d6_r0_s3_sem_0_2633 edge (d12CaseRaw(d6_r0_s3_raw, edge))

end Erdos758.D12Certificate
