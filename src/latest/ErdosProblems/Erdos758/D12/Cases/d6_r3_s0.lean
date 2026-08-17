import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s0_raw
  (include_str "../reduced/d6_r3_s0.cnf")
  (include_str "../reduced/d6_r3_s0.lrat")

def d6_r3_s0_ids : String := include_str "../reduced/d6_r3_s0.ids"

def d6_r3_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r3_s0_sem_0_372 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 0, 372) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 0, 372)

private theorem d6_r3_s0_sem_372_745 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 372, 745) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 372, 745)

private theorem d6_r3_s0_sem_0_745 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 0, 745) := by
  intro h
  exact h.elim (d6_r3_s0_sem_0_372 edge) (d6_r3_s0_sem_372_745 edge)

private theorem d6_r3_s0_sem_745_1117 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 745, 1117) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 745, 1117)

private theorem d6_r3_s0_sem_1117_1490 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 1117, 1490) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 1117, 1490)

private theorem d6_r3_s0_sem_745_1490 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 745, 1490) := by
  intro h
  exact h.elim (d6_r3_s0_sem_745_1117 edge) (d6_r3_s0_sem_1117_1490 edge)

private theorem d6_r3_s0_sem_0_1490 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 0, 1490) := by
  intro h
  exact h.elim (d6_r3_s0_sem_0_745 edge) (d6_r3_s0_sem_745_1490 edge)

private theorem d6_r3_s0_sem_1490_1862 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 1490, 1862) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 1490, 1862)

private theorem d6_r3_s0_sem_1862_2235 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 1862, 2235) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 1862, 2235)

private theorem d6_r3_s0_sem_1490_2235 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 1490, 2235) := by
  intro h
  exact h.elim (d6_r3_s0_sem_1490_1862 edge) (d6_r3_s0_sem_1862_2235 edge)

private theorem d6_r3_s0_sem_2235_2607 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 2235, 2607) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 2235, 2607)

private theorem d6_r3_s0_sem_2607_2980 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 2607, 2980) := by
  exact d12CaseRangeProof(d6_r3_s0_ids, d6_r3_s0_units, edge, 2607, 2980)

private theorem d6_r3_s0_sem_2235_2980 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 2235, 2980) := by
  intro h
  exact h.elim (d6_r3_s0_sem_2235_2607 edge) (d6_r3_s0_sem_2607_2980 edge)

private theorem d6_r3_s0_sem_1490_2980 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 1490, 2980) := by
  intro h
  exact h.elim (d6_r3_s0_sem_1490_2235 edge) (d6_r3_s0_sem_2235_2980 edge)

private theorem d6_r3_s0_sem_0_2980 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s0_ids, d6_r3_s0_units, edge, 0, 2980) := by
  intro h
  exact h.elim (d6_r3_s0_sem_0_1490 edge) (d6_r3_s0_sem_1490_2980 edge)

theorem d6_r3_s0 (edge : Nat → Prop) : D12Outcome edge d6_r3_s0_units := by
  exact d6_r3_s0_sem_0_2980 edge (d12CaseRaw(d6_r3_s0_raw, edge))

end Erdos758.D12Certificate
