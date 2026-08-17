import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r1_s1_raw
  (include_str "../reduced/d7_r1_s1.cnf")
  (include_str "../reduced/d7_r1_s1.lrat")

def d7_r1_s1_ids : String := include_str "../reduced/d7_r1_s1.ids"

def d7_r1_s1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, true), (19, false), (20, false), (21, false)]

private theorem d7_r1_s1_sem_0_456 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 0, 456) := by
  exact d12CaseRangeProof(d7_r1_s1_ids, d7_r1_s1_units, edge, 0, 456)

private theorem d7_r1_s1_sem_456_913 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 456, 913) := by
  exact d12CaseRangeProof(d7_r1_s1_ids, d7_r1_s1_units, edge, 456, 913)

private theorem d7_r1_s1_sem_0_913 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 0, 913) := by
  intro h
  exact h.elim (d7_r1_s1_sem_0_456 edge) (d7_r1_s1_sem_456_913 edge)

private theorem d7_r1_s1_sem_913_1369 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 913, 1369) := by
  exact d12CaseRangeProof(d7_r1_s1_ids, d7_r1_s1_units, edge, 913, 1369)

private theorem d7_r1_s1_sem_1369_1826 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 1369, 1826) := by
  exact d12CaseRangeProof(d7_r1_s1_ids, d7_r1_s1_units, edge, 1369, 1826)

private theorem d7_r1_s1_sem_913_1826 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 913, 1826) := by
  intro h
  exact h.elim (d7_r1_s1_sem_913_1369 edge) (d7_r1_s1_sem_1369_1826 edge)

private theorem d7_r1_s1_sem_0_1826 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s1_ids, d7_r1_s1_units, edge, 0, 1826) := by
  intro h
  exact h.elim (d7_r1_s1_sem_0_913 edge) (d7_r1_s1_sem_913_1826 edge)

theorem d7_r1_s1 (edge : Nat → Prop) : D12Outcome edge d7_r1_s1_units := by
  exact d7_r1_s1_sem_0_1826 edge (d12CaseRaw(d7_r1_s1_raw, edge))

end Erdos758.D12Certificate
