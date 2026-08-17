import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r3_s2_raw
  (include_str "../reduced/d7_r3_s2.cnf")
  (include_str "../reduced/d7_r3_s2.lrat")

def d7_r3_s2_ids : String := include_str "../reduced/d7_r3_s2.ids"

def d7_r3_s2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, true), (19, true), (20, false), (21, false)]

private theorem d7_r3_s2_sem_0_362 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 0, 362) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 0, 362)

private theorem d7_r3_s2_sem_362_725 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 362, 725) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 362, 725)

private theorem d7_r3_s2_sem_0_725 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 0, 725) := by
  intro h
  exact h.elim (d7_r3_s2_sem_0_362 edge) (d7_r3_s2_sem_362_725 edge)

private theorem d7_r3_s2_sem_725_1088 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 725, 1088) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 725, 1088)

private theorem d7_r3_s2_sem_1088_1451 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 1088, 1451) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 1088, 1451)

private theorem d7_r3_s2_sem_725_1451 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 725, 1451) := by
  intro h
  exact h.elim (d7_r3_s2_sem_725_1088 edge) (d7_r3_s2_sem_1088_1451 edge)

private theorem d7_r3_s2_sem_0_1451 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 0, 1451) := by
  intro h
  exact h.elim (d7_r3_s2_sem_0_725 edge) (d7_r3_s2_sem_725_1451 edge)

private theorem d7_r3_s2_sem_1451_1813 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 1451, 1813) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 1451, 1813)

private theorem d7_r3_s2_sem_1813_2176 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 1813, 2176) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 1813, 2176)

private theorem d7_r3_s2_sem_1451_2176 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 1451, 2176) := by
  intro h
  exact h.elim (d7_r3_s2_sem_1451_1813 edge) (d7_r3_s2_sem_1813_2176 edge)

private theorem d7_r3_s2_sem_2176_2539 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 2176, 2539) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 2176, 2539)

private theorem d7_r3_s2_sem_2539_2902 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 2539, 2902) := by
  exact d12CaseRangeProof(d7_r3_s2_ids, d7_r3_s2_units, edge, 2539, 2902)

private theorem d7_r3_s2_sem_2176_2902 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 2176, 2902) := by
  intro h
  exact h.elim (d7_r3_s2_sem_2176_2539 edge) (d7_r3_s2_sem_2539_2902 edge)

private theorem d7_r3_s2_sem_1451_2902 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 1451, 2902) := by
  intro h
  exact h.elim (d7_r3_s2_sem_1451_2176 edge) (d7_r3_s2_sem_2176_2902 edge)

private theorem d7_r3_s2_sem_0_2902 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s2_ids, d7_r3_s2_units, edge, 0, 2902) := by
  intro h
  exact h.elim (d7_r3_s2_sem_0_1451 edge) (d7_r3_s2_sem_1451_2902 edge)

theorem d7_r3_s2 (edge : Nat → Prop) : D12Outcome edge d7_r3_s2_units := by
  exact d7_r3_s2_sem_0_2902 edge (d12CaseRaw(d7_r3_s2_raw, edge))

end Erdos758.D12Certificate
