import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s3_t2_raw
  (include_str "../reduced/d6_r2_s3_t2.cnf")
  (include_str "../reduced/d6_r2_s3_t2.lrat")

def d6_r2_s3_t2_ids : String := include_str "../reduced/d6_r2_s3_t2.ids"

def d6_r2_s3_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (23, true), (24, true), (25, false)]

private theorem d6_r2_s3_t2_sem_0_283 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 0, 283) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 0, 283)

private theorem d6_r2_s3_t2_sem_283_567 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 283, 567) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 283, 567)

private theorem d6_r2_s3_t2_sem_0_567 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 0, 567) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_0_283 edge) (d6_r2_s3_t2_sem_283_567 edge)

private theorem d6_r2_s3_t2_sem_567_850 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 567, 850) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 567, 850)

private theorem d6_r2_s3_t2_sem_850_1134 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 850, 1134) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 850, 1134)

private theorem d6_r2_s3_t2_sem_567_1134 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 567, 1134) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_567_850 edge) (d6_r2_s3_t2_sem_850_1134 edge)

private theorem d6_r2_s3_t2_sem_0_1134 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 0, 1134) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_0_567 edge) (d6_r2_s3_t2_sem_567_1134 edge)

private theorem d6_r2_s3_t2_sem_1134_1417 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1134, 1417) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1134, 1417)

private theorem d6_r2_s3_t2_sem_1417_1701 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1417, 1701) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1417, 1701)

private theorem d6_r2_s3_t2_sem_1134_1701 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1134, 1701) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_1134_1417 edge) (d6_r2_s3_t2_sem_1417_1701 edge)

private theorem d6_r2_s3_t2_sem_1701_1984 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1701, 1984) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1701, 1984)

private theorem d6_r2_s3_t2_sem_1984_2268 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1984, 2268) := by
  exact d12CaseRangeProof(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1984, 2268)

private theorem d6_r2_s3_t2_sem_1701_2268 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1701, 2268) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_1701_1984 edge) (d6_r2_s3_t2_sem_1984_2268 edge)

private theorem d6_r2_s3_t2_sem_1134_2268 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 1134, 2268) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_1134_1701 edge) (d6_r2_s3_t2_sem_1701_2268 edge)

private theorem d6_r2_s3_t2_sem_0_2268 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t2_ids, d6_r2_s3_t2_units, edge, 0, 2268) := by
  intro h
  exact h.elim (d6_r2_s3_t2_sem_0_1134 edge) (d6_r2_s3_t2_sem_1134_2268 edge)

theorem d6_r2_s3_t2 (edge : Nat → Prop) : D12Outcome edge d6_r2_s3_t2_units := by
  exact d6_r2_s3_t2_sem_0_2268 edge (d12CaseRaw(d6_r2_s3_t2_raw, edge))

end Erdos758.D12Certificate
