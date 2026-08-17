import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r3_s3_raw
  (include_str "../reduced/d7_r3_s3.cnf")
  (include_str "../reduced/d7_r3_s3.lrat")

def d7_r3_s3_ids : String := include_str "../reduced/d7_r3_s3.ids"

def d7_r3_s3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false)]

private theorem d7_r3_s3_sem_0_388 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 0, 388) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 0, 388)

private theorem d7_r3_s3_sem_388_777 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 388, 777) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 388, 777)

private theorem d7_r3_s3_sem_0_777 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 0, 777) := by
  intro h
  exact h.elim (d7_r3_s3_sem_0_388 edge) (d7_r3_s3_sem_388_777 edge)

private theorem d7_r3_s3_sem_777_1166 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 777, 1166) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 777, 1166)

private theorem d7_r3_s3_sem_1166_1555 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 1166, 1555) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 1166, 1555)

private theorem d7_r3_s3_sem_777_1555 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 777, 1555) := by
  intro h
  exact h.elim (d7_r3_s3_sem_777_1166 edge) (d7_r3_s3_sem_1166_1555 edge)

private theorem d7_r3_s3_sem_0_1555 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 0, 1555) := by
  intro h
  exact h.elim (d7_r3_s3_sem_0_777 edge) (d7_r3_s3_sem_777_1555 edge)

private theorem d7_r3_s3_sem_1555_1943 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 1555, 1943) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 1555, 1943)

private theorem d7_r3_s3_sem_1943_2332 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 1943, 2332) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 1943, 2332)

private theorem d7_r3_s3_sem_1555_2332 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 1555, 2332) := by
  intro h
  exact h.elim (d7_r3_s3_sem_1555_1943 edge) (d7_r3_s3_sem_1943_2332 edge)

private theorem d7_r3_s3_sem_2332_2721 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 2332, 2721) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 2332, 2721)

private theorem d7_r3_s3_sem_2721_3110 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 2721, 3110) := by
  exact d12CaseRangeProof(d7_r3_s3_ids, d7_r3_s3_units, edge, 2721, 3110)

private theorem d7_r3_s3_sem_2332_3110 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 2332, 3110) := by
  intro h
  exact h.elim (d7_r3_s3_sem_2332_2721 edge) (d7_r3_s3_sem_2721_3110 edge)

private theorem d7_r3_s3_sem_1555_3110 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 1555, 3110) := by
  intro h
  exact h.elim (d7_r3_s3_sem_1555_2332 edge) (d7_r3_s3_sem_2332_3110 edge)

private theorem d7_r3_s3_sem_0_3110 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s3_ids, d7_r3_s3_units, edge, 0, 3110) := by
  intro h
  exact h.elim (d7_r3_s3_sem_0_1555 edge) (d7_r3_s3_sem_1555_3110 edge)

theorem d7_r3_s3 (edge : Nat → Prop) : D12Outcome edge d7_r3_s3_units := by
  exact d7_r3_s3_sem_0_3110 edge (d12CaseRaw(d7_r3_s3_raw, edge))

end Erdos758.D12Certificate
