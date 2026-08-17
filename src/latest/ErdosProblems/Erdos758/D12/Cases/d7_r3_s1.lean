import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r3_s1_raw
  (include_str "../reduced/d7_r3_s1.cnf")
  (include_str "../reduced/d7_r3_s1.lrat")

def d7_r3_s1_ids : String := include_str "../reduced/d7_r3_s1.ids"

def d7_r3_s1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, true), (19, false), (20, false), (21, false)]

private theorem d7_r3_s1_sem_0_321 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 0, 321) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 0, 321)

private theorem d7_r3_s1_sem_321_642 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 321, 642) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 321, 642)

private theorem d7_r3_s1_sem_0_642 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 0, 642) := by
  intro h
  exact h.elim (d7_r3_s1_sem_0_321 edge) (d7_r3_s1_sem_321_642 edge)

private theorem d7_r3_s1_sem_642_963 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 642, 963) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 642, 963)

private theorem d7_r3_s1_sem_963_1284 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 963, 1284) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 963, 1284)

private theorem d7_r3_s1_sem_642_1284 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 642, 1284) := by
  intro h
  exact h.elim (d7_r3_s1_sem_642_963 edge) (d7_r3_s1_sem_963_1284 edge)

private theorem d7_r3_s1_sem_0_1284 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 0, 1284) := by
  intro h
  exact h.elim (d7_r3_s1_sem_0_642 edge) (d7_r3_s1_sem_642_1284 edge)

private theorem d7_r3_s1_sem_1284_1605 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1284, 1605) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 1284, 1605)

private theorem d7_r3_s1_sem_1605_1926 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1605, 1926) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 1605, 1926)

private theorem d7_r3_s1_sem_1284_1926 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1284, 1926) := by
  intro h
  exact h.elim (d7_r3_s1_sem_1284_1605 edge) (d7_r3_s1_sem_1605_1926 edge)

private theorem d7_r3_s1_sem_1926_2247 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1926, 2247) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 1926, 2247)

private theorem d7_r3_s1_sem_2247_2568 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 2247, 2568) := by
  exact d12CaseRangeProof(d7_r3_s1_ids, d7_r3_s1_units, edge, 2247, 2568)

private theorem d7_r3_s1_sem_1926_2568 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1926, 2568) := by
  intro h
  exact h.elim (d7_r3_s1_sem_1926_2247 edge) (d7_r3_s1_sem_2247_2568 edge)

private theorem d7_r3_s1_sem_1284_2568 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 1284, 2568) := by
  intro h
  exact h.elim (d7_r3_s1_sem_1284_1926 edge) (d7_r3_s1_sem_1926_2568 edge)

private theorem d7_r3_s1_sem_0_2568 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s1_ids, d7_r3_s1_units, edge, 0, 2568) := by
  intro h
  exact h.elim (d7_r3_s1_sem_0_1284 edge) (d7_r3_s1_sem_1284_2568 edge)

theorem d7_r3_s1 (edge : Nat → Prop) : D12Outcome edge d7_r3_s1_units := by
  exact d7_r3_s1_sem_0_2568 edge (d12CaseRaw(d7_r3_s1_raw, edge))

end Erdos758.D12Certificate
