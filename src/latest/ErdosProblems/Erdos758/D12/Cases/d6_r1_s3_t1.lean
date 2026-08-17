import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s3_t1_raw
  (include_str "../reduced/d6_r1_s3_t1.cnf")
  (include_str "../reduced/d6_r1_s3_t1.lrat")

def d6_r1_s3_t1_ids : String := include_str "../reduced/d6_r1_s3_t1.ids"

def d6_r1_s3_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (22, true), (23, false), (24, false), (25, false)]

private theorem d6_r1_s3_t1_sem_0_292 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 0, 292) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 0, 292)

private theorem d6_r1_s3_t1_sem_292_584 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 292, 584) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 292, 584)

private theorem d6_r1_s3_t1_sem_0_584 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 0, 584) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_0_292 edge) (d6_r1_s3_t1_sem_292_584 edge)

private theorem d6_r1_s3_t1_sem_584_876 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 584, 876) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 584, 876)

private theorem d6_r1_s3_t1_sem_876_1169 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 876, 1169) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 876, 1169)

private theorem d6_r1_s3_t1_sem_584_1169 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 584, 1169) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_584_876 edge) (d6_r1_s3_t1_sem_876_1169 edge)

private theorem d6_r1_s3_t1_sem_0_1169 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 0, 1169) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_0_584 edge) (d6_r1_s3_t1_sem_584_1169 edge)

private theorem d6_r1_s3_t1_sem_1169_1461 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1169, 1461) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1169, 1461)

private theorem d6_r1_s3_t1_sem_1461_1753 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1461, 1753) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1461, 1753)

private theorem d6_r1_s3_t1_sem_1169_1753 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1169, 1753) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_1169_1461 edge) (d6_r1_s3_t1_sem_1461_1753 edge)

private theorem d6_r1_s3_t1_sem_1753_2045 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1753, 2045) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1753, 2045)

private theorem d6_r1_s3_t1_sem_2045_2338 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 2045, 2338) := by
  exact d12CaseRangeProof(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 2045, 2338)

private theorem d6_r1_s3_t1_sem_1753_2338 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1753, 2338) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_1753_2045 edge) (d6_r1_s3_t1_sem_2045_2338 edge)

private theorem d6_r1_s3_t1_sem_1169_2338 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 1169, 2338) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_1169_1753 edge) (d6_r1_s3_t1_sem_1753_2338 edge)

private theorem d6_r1_s3_t1_sem_0_2338 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s3_t1_ids, d6_r1_s3_t1_units, edge, 0, 2338) := by
  intro h
  exact h.elim (d6_r1_s3_t1_sem_0_1169 edge) (d6_r1_s3_t1_sem_1169_2338 edge)

theorem d6_r1_s3_t1 (edge : Nat → Prop) : D12Outcome edge d6_r1_s3_t1_units := by
  exact d6_r1_s3_t1_sem_0_2338 edge (d12CaseRaw(d6_r1_s3_t1_raw, edge))

end Erdos758.D12Certificate
