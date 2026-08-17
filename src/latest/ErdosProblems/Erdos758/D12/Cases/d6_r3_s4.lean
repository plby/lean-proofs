import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s4_raw
  (include_str "../reduced/d6_r3_s4.cnf")
  (include_str "../reduced/d6_r3_s4.lrat")

def d6_r3_s4_ids : String := include_str "../reduced/d6_r3_s4.ids"

def d6_r3_s4_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false)]

private theorem d6_r3_s4_sem_0_316 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 0, 316) := by
  exact d12CaseRangeProof(d6_r3_s4_ids, d6_r3_s4_units, edge, 0, 316)

private theorem d6_r3_s4_sem_316_633 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 316, 633) := by
  exact d12CaseRangeProof(d6_r3_s4_ids, d6_r3_s4_units, edge, 316, 633)

private theorem d6_r3_s4_sem_0_633 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 0, 633) := by
  intro h
  exact h.elim (d6_r3_s4_sem_0_316 edge) (d6_r3_s4_sem_316_633 edge)

private theorem d6_r3_s4_sem_633_949 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 633, 949) := by
  exact d12CaseRangeProof(d6_r3_s4_ids, d6_r3_s4_units, edge, 633, 949)

private theorem d6_r3_s4_sem_949_1266 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 949, 1266) := by
  exact d12CaseRangeProof(d6_r3_s4_ids, d6_r3_s4_units, edge, 949, 1266)

private theorem d6_r3_s4_sem_633_1266 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 633, 1266) := by
  intro h
  exact h.elim (d6_r3_s4_sem_633_949 edge) (d6_r3_s4_sem_949_1266 edge)

private theorem d6_r3_s4_sem_0_1266 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s4_ids, d6_r3_s4_units, edge, 0, 1266) := by
  intro h
  exact h.elim (d6_r3_s4_sem_0_633 edge) (d6_r3_s4_sem_633_1266 edge)

theorem d6_r3_s4 (edge : Nat → Prop) : D12Outcome edge d6_r3_s4_units := by
  exact d6_r3_s4_sem_0_1266 edge (d12CaseRaw(d6_r3_s4_raw, edge))

end Erdos758.D12Certificate
