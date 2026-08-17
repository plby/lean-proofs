import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r1_s3_raw
  (include_str "../reduced/d7_r1_s3.cnf")
  (include_str "../reduced/d7_r1_s3.lrat")

def d7_r1_s3_ids : String := include_str "../reduced/d7_r1_s3.ids"

def d7_r1_s3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, false)]

private theorem d7_r1_s3_sem_0_312 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 0, 312) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 0, 312)

private theorem d7_r1_s3_sem_312_624 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 312, 624) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 312, 624)

private theorem d7_r1_s3_sem_0_624 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 0, 624) := by
  intro h
  exact h.elim (d7_r1_s3_sem_0_312 edge) (d7_r1_s3_sem_312_624 edge)

private theorem d7_r1_s3_sem_624_936 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 624, 936) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 624, 936)

private theorem d7_r1_s3_sem_936_1248 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 936, 1248) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 936, 1248)

private theorem d7_r1_s3_sem_624_1248 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 624, 1248) := by
  intro h
  exact h.elim (d7_r1_s3_sem_624_936 edge) (d7_r1_s3_sem_936_1248 edge)

private theorem d7_r1_s3_sem_0_1248 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 0, 1248) := by
  intro h
  exact h.elim (d7_r1_s3_sem_0_624 edge) (d7_r1_s3_sem_624_1248 edge)

private theorem d7_r1_s3_sem_1248_1560 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1248, 1560) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 1248, 1560)

private theorem d7_r1_s3_sem_1560_1872 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1560, 1872) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 1560, 1872)

private theorem d7_r1_s3_sem_1248_1872 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1248, 1872) := by
  intro h
  exact h.elim (d7_r1_s3_sem_1248_1560 edge) (d7_r1_s3_sem_1560_1872 edge)

private theorem d7_r1_s3_sem_1872_2184 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1872, 2184) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 1872, 2184)

private theorem d7_r1_s3_sem_2184_2497 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 2184, 2497) := by
  exact d12CaseRangeProof(d7_r1_s3_ids, d7_r1_s3_units, edge, 2184, 2497)

private theorem d7_r1_s3_sem_1872_2497 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1872, 2497) := by
  intro h
  exact h.elim (d7_r1_s3_sem_1872_2184 edge) (d7_r1_s3_sem_2184_2497 edge)

private theorem d7_r1_s3_sem_1248_2497 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 1248, 2497) := by
  intro h
  exact h.elim (d7_r1_s3_sem_1248_1872 edge) (d7_r1_s3_sem_1872_2497 edge)

private theorem d7_r1_s3_sem_0_2497 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s3_ids, d7_r1_s3_units, edge, 0, 2497) := by
  intro h
  exact h.elim (d7_r1_s3_sem_0_1248 edge) (d7_r1_s3_sem_1248_2497 edge)

theorem d7_r1_s3 (edge : Nat → Prop) : D12Outcome edge d7_r1_s3_units := by
  exact d7_r1_s3_sem_0_2497 edge (d12CaseRaw(d7_r1_s3_raw, edge))

end Erdos758.D12Certificate
