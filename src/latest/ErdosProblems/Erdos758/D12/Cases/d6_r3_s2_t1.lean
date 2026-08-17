import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s2_t1_raw
  (include_str "../reduced/d6_r3_s2_t1.cnf")
  (include_str "../reduced/d6_r3_s2_t1.lrat")

def d6_r3_s2_t1_ids : String := include_str "../reduced/d6_r3_s2_t1.ids"

def d6_r3_s2_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (24, true), (25, false)]

private theorem d6_r3_s2_t1_sem_0_293 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 0, 293) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 0, 293)

private theorem d6_r3_s2_t1_sem_293_586 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 293, 586) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 293, 586)

private theorem d6_r3_s2_t1_sem_0_586 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 0, 586) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_0_293 edge) (d6_r3_s2_t1_sem_293_586 edge)

private theorem d6_r3_s2_t1_sem_586_879 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 586, 879) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 586, 879)

private theorem d6_r3_s2_t1_sem_879_1173 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 879, 1173) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 879, 1173)

private theorem d6_r3_s2_t1_sem_586_1173 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 586, 1173) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_586_879 edge) (d6_r3_s2_t1_sem_879_1173 edge)

private theorem d6_r3_s2_t1_sem_0_1173 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 0, 1173) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_0_586 edge) (d6_r3_s2_t1_sem_586_1173 edge)

private theorem d6_r3_s2_t1_sem_1173_1466 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1173, 1466) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1173, 1466)

private theorem d6_r3_s2_t1_sem_1466_1760 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1466, 1760) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1466, 1760)

private theorem d6_r3_s2_t1_sem_1173_1760 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1173, 1760) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_1173_1466 edge) (d6_r3_s2_t1_sem_1466_1760 edge)

private theorem d6_r3_s2_t1_sem_1760_2053 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1760, 2053) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1760, 2053)

private theorem d6_r3_s2_t1_sem_2053_2347 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 2053, 2347) := by
  exact d12CaseRangeProof(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 2053, 2347)

private theorem d6_r3_s2_t1_sem_1760_2347 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1760, 2347) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_1760_2053 edge) (d6_r3_s2_t1_sem_2053_2347 edge)

private theorem d6_r3_s2_t1_sem_1173_2347 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 1173, 2347) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_1173_1760 edge) (d6_r3_s2_t1_sem_1760_2347 edge)

private theorem d6_r3_s2_t1_sem_0_2347 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t1_ids, d6_r3_s2_t1_units, edge, 0, 2347) := by
  intro h
  exact h.elim (d6_r3_s2_t1_sem_0_1173 edge) (d6_r3_s2_t1_sem_1173_2347 edge)

theorem d6_r3_s2_t1 (edge : Nat → Prop) : D12Outcome edge d6_r3_s2_t1_units := by
  exact d6_r3_s2_t1_sem_0_2347 edge (d12CaseRaw(d6_r3_s2_t1_raw, edge))

end Erdos758.D12Certificate
