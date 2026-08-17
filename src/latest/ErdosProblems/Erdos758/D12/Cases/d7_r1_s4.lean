import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r1_s4_raw
  (include_str "../reduced/d7_r1_s4.cnf")
  (include_str "../reduced/d7_r1_s4.lrat")

def d7_r1_s4_ids : String := include_str "../reduced/d7_r1_s4.ids"

def d7_r1_s4_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, true), (21, true)]

private theorem d7_r1_s4_sem_0_271 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 0, 271) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 0, 271)

private theorem d7_r1_s4_sem_271_543 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 271, 543) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 271, 543)

private theorem d7_r1_s4_sem_0_543 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 0, 543) := by
  intro h
  exact h.elim (d7_r1_s4_sem_0_271 edge) (d7_r1_s4_sem_271_543 edge)

private theorem d7_r1_s4_sem_543_814 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 543, 814) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 543, 814)

private theorem d7_r1_s4_sem_814_1086 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 814, 1086) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 814, 1086)

private theorem d7_r1_s4_sem_543_1086 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 543, 1086) := by
  intro h
  exact h.elim (d7_r1_s4_sem_543_814 edge) (d7_r1_s4_sem_814_1086 edge)

private theorem d7_r1_s4_sem_0_1086 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 0, 1086) := by
  intro h
  exact h.elim (d7_r1_s4_sem_0_543 edge) (d7_r1_s4_sem_543_1086 edge)

private theorem d7_r1_s4_sem_1086_1357 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1086, 1357) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 1086, 1357)

private theorem d7_r1_s4_sem_1357_1629 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1357, 1629) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 1357, 1629)

private theorem d7_r1_s4_sem_1086_1629 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1086, 1629) := by
  intro h
  exact h.elim (d7_r1_s4_sem_1086_1357 edge) (d7_r1_s4_sem_1357_1629 edge)

private theorem d7_r1_s4_sem_1629_1900 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1629, 1900) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 1629, 1900)

private theorem d7_r1_s4_sem_1900_2172 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1900, 2172) := by
  exact d12CaseRangeProof(d7_r1_s4_ids, d7_r1_s4_units, edge, 1900, 2172)

private theorem d7_r1_s4_sem_1629_2172 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1629, 2172) := by
  intro h
  exact h.elim (d7_r1_s4_sem_1629_1900 edge) (d7_r1_s4_sem_1900_2172 edge)

private theorem d7_r1_s4_sem_1086_2172 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 1086, 2172) := by
  intro h
  exact h.elim (d7_r1_s4_sem_1086_1629 edge) (d7_r1_s4_sem_1629_2172 edge)

private theorem d7_r1_s4_sem_0_2172 (edge : Nat → Prop) :
    d12CaseRange(d7_r1_s4_ids, d7_r1_s4_units, edge, 0, 2172) := by
  intro h
  exact h.elim (d7_r1_s4_sem_0_1086 edge) (d7_r1_s4_sem_1086_2172 edge)

theorem d7_r1_s4 (edge : Nat → Prop) : D12Outcome edge d7_r1_s4_units := by
  exact d7_r1_s4_sem_0_2172 edge (d12CaseRaw(d7_r1_s4_raw, edge))

end Erdos758.D12Certificate
