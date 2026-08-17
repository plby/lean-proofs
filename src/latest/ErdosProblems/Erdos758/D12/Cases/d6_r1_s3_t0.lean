import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s3_t0_raw
  (include_str "../reduced/d6_r1_s3_t0.cnf")
  (include_str "../reduced/d6_r1_s3_t0.lrat")

def d6_r1_s3_t0_ids : String := include_str "../reduced/d6_r1_s3_t0.ids"

def d6_r1_s3_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (22, false), (23, false), (24, false), (25, false)]

private theorem d6_r1_s3_t0_sem_0_294 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 0, 294) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 0, 294)

private theorem d6_r1_s3_t0_sem_294_588 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 294, 588) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 294, 588)

private theorem d6_r1_s3_t0_sem_0_588 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 0, 588) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_0_294 edge) (d6_r1_s3_t0_sem_294_588 edge)

private theorem d6_r1_s3_t0_sem_588_882 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 588, 882) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 588, 882)

private theorem d6_r1_s3_t0_sem_882_1176 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 882, 1176) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 882, 1176)

private theorem d6_r1_s3_t0_sem_588_1176 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 588, 1176) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_588_882 edge) (d6_r1_s3_t0_sem_882_1176 edge)

private theorem d6_r1_s3_t0_sem_0_1176 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 0, 1176) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_0_588 edge) (d6_r1_s3_t0_sem_588_1176 edge)

private theorem d6_r1_s3_t0_sem_1176_1470 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1176, 1470) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1176, 1470)

private theorem d6_r1_s3_t0_sem_1470_1764 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1470, 1764) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1470, 1764)

private theorem d6_r1_s3_t0_sem_1176_1764 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1176, 1764) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_1176_1470 edge) (d6_r1_s3_t0_sem_1470_1764 edge)

private theorem d6_r1_s3_t0_sem_1764_2058 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1764, 2058) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1764, 2058)

private theorem d6_r1_s3_t0_sem_2058_2353 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 2058, 2353) := by
  exact d12CaseRangeProof(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 2058, 2353)

private theorem d6_r1_s3_t0_sem_1764_2353 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1764, 2353) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_1764_2058 edge) (d6_r1_s3_t0_sem_2058_2353 edge)

private theorem d6_r1_s3_t0_sem_1176_2353 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 1176, 2353) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_1176_1764 edge) (d6_r1_s3_t0_sem_1764_2353 edge)

private theorem d6_r1_s3_t0_sem_0_2353 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t0_ids, d6_r1_s3_t0_units, edge, 0, 2353) := by
  intro h
  exact h.elim (d6_r1_s3_t0_sem_0_1176 edge) (d6_r1_s3_t0_sem_1176_2353 edge)

theorem d6_r1_s3_t0 (edge : Nat → Prop) : D12Outcome edge d6_r1_s3_t0_units := by
  exact d6_r1_s3_t0_sem_0_2353 edge (d12CaseRaw(d6_r1_s3_t0_raw, edge))

end Erdos758.D12Certificate
