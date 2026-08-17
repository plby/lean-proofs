import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s4_t2_raw
  (include_str "../reduced/d6_r1_s4_t2.cnf")
  (include_str "../reduced/d6_r1_s4_t2.lrat")

def d6_r1_s4_t2_ids : String := include_str "../reduced/d6_r1_s4_t2.ids"

def d6_r1_s4_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (22, true), (23, true), (24, false), (25, false)]

private theorem d6_r1_s4_t2_sem_0_490 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 0, 490) := by
  exact d12CaseRangeProof(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 0, 490)

private theorem d6_r1_s4_t2_sem_490_981 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 490, 981) := by
  exact d12CaseRangeProof(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 490, 981)

private theorem d6_r1_s4_t2_sem_0_981 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 0, 981) := by
  intro h
  exact h.elim (d6_r1_s4_t2_sem_0_490 edge) (d6_r1_s4_t2_sem_490_981 edge)

private theorem d6_r1_s4_t2_sem_981_1472 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 981, 1472) := by
  exact d12CaseRangeProof(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 981, 1472)

private theorem d6_r1_s4_t2_sem_1472_1963 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 1472, 1963) := by
  exact d12CaseRangeProof(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 1472, 1963)

private theorem d6_r1_s4_t2_sem_981_1963 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 981, 1963) := by
  intro h
  exact h.elim (d6_r1_s4_t2_sem_981_1472 edge) (d6_r1_s4_t2_sem_1472_1963 edge)

private theorem d6_r1_s4_t2_sem_0_1963 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t2_ids, d6_r1_s4_t2_units, edge, 0, 1963) := by
  intro h
  exact h.elim (d6_r1_s4_t2_sem_0_981 edge) (d6_r1_s4_t2_sem_981_1963 edge)

theorem d6_r1_s4_t2 (edge : Nat → Prop) : D12Outcome edge d6_r1_s4_t2_units := by
  exact d6_r1_s4_t2_sem_0_1963 edge (d12CaseRaw(d6_r1_s4_t2_raw, edge))

end Erdos758.D12Certificate
