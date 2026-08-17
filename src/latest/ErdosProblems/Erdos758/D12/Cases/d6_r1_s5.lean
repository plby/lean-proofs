import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s5_raw
  (include_str "../reduced/d6_r1_s5.cnf")
  (include_str "../reduced/d6_r1_s5.lrat")

def d6_r1_s5_ids : String := include_str "../reduced/d6_r1_s5.ids"

def d6_r1_s5_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, true)]

private theorem d6_r1_s5_sem_0_259 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 0, 259) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 0, 259)

private theorem d6_r1_s5_sem_259_519 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 259, 519) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 259, 519)

private theorem d6_r1_s5_sem_0_519 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 0, 519) := by
  intro h
  exact h.elim (d6_r1_s5_sem_0_259 edge) (d6_r1_s5_sem_259_519 edge)

private theorem d6_r1_s5_sem_519_779 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 519, 779) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 519, 779)

private theorem d6_r1_s5_sem_779_1039 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 779, 1039) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 779, 1039)

private theorem d6_r1_s5_sem_519_1039 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 519, 1039) := by
  intro h
  exact h.elim (d6_r1_s5_sem_519_779 edge) (d6_r1_s5_sem_779_1039 edge)

private theorem d6_r1_s5_sem_0_1039 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 0, 1039) := by
  intro h
  exact h.elim (d6_r1_s5_sem_0_519 edge) (d6_r1_s5_sem_519_1039 edge)

private theorem d6_r1_s5_sem_1039_1298 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1039, 1298) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 1039, 1298)

private theorem d6_r1_s5_sem_1298_1558 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1298, 1558) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 1298, 1558)

private theorem d6_r1_s5_sem_1039_1558 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1039, 1558) := by
  intro h
  exact h.elim (d6_r1_s5_sem_1039_1298 edge) (d6_r1_s5_sem_1298_1558 edge)

private theorem d6_r1_s5_sem_1558_1818 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1558, 1818) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 1558, 1818)

private theorem d6_r1_s5_sem_1818_2078 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1818, 2078) := by
  exact d12CaseRangeProof(d6_r1_s5_ids, d6_r1_s5_units, edge, 1818, 2078)

private theorem d6_r1_s5_sem_1558_2078 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1558, 2078) := by
  intro h
  exact h.elim (d6_r1_s5_sem_1558_1818 edge) (d6_r1_s5_sem_1818_2078 edge)

private theorem d6_r1_s5_sem_1039_2078 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 1039, 2078) := by
  intro h
  exact h.elim (d6_r1_s5_sem_1039_1558 edge) (d6_r1_s5_sem_1558_2078 edge)

private theorem d6_r1_s5_sem_0_2078 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s5_ids, d6_r1_s5_units, edge, 0, 2078) := by
  intro h
  exact h.elim (d6_r1_s5_sem_0_1039 edge) (d6_r1_s5_sem_1039_2078 edge)

theorem d6_r1_s5 (edge : Nat → Prop) : D12Outcome edge d6_r1_s5_units := by
  exact d6_r1_s5_sem_0_2078 edge (d12CaseRaw(d6_r1_s5_raw, edge))

end Erdos758.D12Certificate
