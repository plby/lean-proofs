import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r1_s0_raw
  (include_str "../reduced/d7_r1_s0.cnf")
  (include_str "../reduced/d7_r1_s0.lrat")

def d7_r1_s0_ids : String := include_str "../reduced/d7_r1_s0.ids"

def d7_r1_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d7_r1_s0_sem_0_322 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 0, 322) := by
  exact d12CaseRangeProof(d7_r1_s0_ids, d7_r1_s0_units, edge, 0, 322)

private theorem d7_r1_s0_sem_322_645 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 322, 645) := by
  exact d12CaseRangeProof(d7_r1_s0_ids, d7_r1_s0_units, edge, 322, 645)

private theorem d7_r1_s0_sem_0_645 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 0, 645) := by
  intro h
  exact h.elim (d7_r1_s0_sem_0_322 edge) (d7_r1_s0_sem_322_645 edge)

private theorem d7_r1_s0_sem_645_967 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 645, 967) := by
  exact d12CaseRangeProof(d7_r1_s0_ids, d7_r1_s0_units, edge, 645, 967)

private theorem d7_r1_s0_sem_967_1290 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 967, 1290) := by
  exact d12CaseRangeProof(d7_r1_s0_ids, d7_r1_s0_units, edge, 967, 1290)

private theorem d7_r1_s0_sem_645_1290 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 645, 1290) := by
  intro h
  exact h.elim (d7_r1_s0_sem_645_967 edge) (d7_r1_s0_sem_967_1290 edge)

private theorem d7_r1_s0_sem_0_1290 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s0_ids, d7_r1_s0_units, edge, 0, 1290) := by
  intro h
  exact h.elim (d7_r1_s0_sem_0_645 edge) (d7_r1_s0_sem_645_1290 edge)

theorem d7_r1_s0 (edge : Nat → Prop) : D12Outcome edge d7_r1_s0_units := by
  exact d7_r1_s0_sem_0_1290 edge (d12CaseRaw(d7_r1_s0_raw, edge))

end Erdos758.D12Certificate
