import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s3_raw
  (include_str "../reduced/d6_r3_s3.cnf")
  (include_str "../reduced/d6_r3_s3.lrat")

def d6_r3_s3_ids : String := include_str "../reduced/d6_r3_s3.ids"

def d6_r3_s3_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false)]

private theorem d6_r3_s3_sem_0_356 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 0, 356) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 0, 356)

private theorem d6_r3_s3_sem_356_713 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 356, 713) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 356, 713)

private theorem d6_r3_s3_sem_0_713 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 0, 713) := by
  intro h
  exact h.elim (d6_r3_s3_sem_0_356 edge) (d6_r3_s3_sem_356_713 edge)

private theorem d6_r3_s3_sem_713_1070 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 713, 1070) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 713, 1070)

private theorem d6_r3_s3_sem_1070_1427 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 1070, 1427) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 1070, 1427)

private theorem d6_r3_s3_sem_713_1427 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 713, 1427) := by
  intro h
  exact h.elim (d6_r3_s3_sem_713_1070 edge) (d6_r3_s3_sem_1070_1427 edge)

private theorem d6_r3_s3_sem_0_1427 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 0, 1427) := by
  intro h
  exact h.elim (d6_r3_s3_sem_0_713 edge) (d6_r3_s3_sem_713_1427 edge)

private theorem d6_r3_s3_sem_1427_1784 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 1427, 1784) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 1427, 1784)

private theorem d6_r3_s3_sem_1784_2141 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 1784, 2141) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 1784, 2141)

private theorem d6_r3_s3_sem_1427_2141 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 1427, 2141) := by
  intro h
  exact h.elim (d6_r3_s3_sem_1427_1784 edge) (d6_r3_s3_sem_1784_2141 edge)

private theorem d6_r3_s3_sem_2141_2498 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 2141, 2498) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 2141, 2498)

private theorem d6_r3_s3_sem_2498_2855 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 2498, 2855) := by
  exact d12CaseRangeProof(d6_r3_s3_ids, d6_r3_s3_units, edge, 2498, 2855)

private theorem d6_r3_s3_sem_2141_2855 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 2141, 2855) := by
  intro h
  exact h.elim (d6_r3_s3_sem_2141_2498 edge) (d6_r3_s3_sem_2498_2855 edge)

private theorem d6_r3_s3_sem_1427_2855 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 1427, 2855) := by
  intro h
  exact h.elim (d6_r3_s3_sem_1427_2141 edge) (d6_r3_s3_sem_2141_2855 edge)

private theorem d6_r3_s3_sem_0_2855 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s3_ids, d6_r3_s3_units, edge, 0, 2855) := by
  intro h
  exact h.elim (d6_r3_s3_sem_0_1427 edge) (d6_r3_s3_sem_1427_2855 edge)

theorem d6_r3_s3 (edge : Nat → Prop) : D12Outcome edge d6_r3_s3_units := by
  exact d6_r3_s3_sem_0_2855 edge (d12CaseRaw(d6_r3_s3_raw, edge))

end Erdos758.D12Certificate
