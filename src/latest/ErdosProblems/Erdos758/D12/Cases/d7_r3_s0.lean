import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r3_s0_raw
  (include_str "../reduced/d7_r3_s0.cnf")
  (include_str "../reduced/d7_r3_s0.lrat")

def d7_r3_s0_ids : String := include_str "../reduced/d7_r3_s0.ids"

def d7_r3_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d7_r3_s0_sem_0_306 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 0, 306) := by
  exact d12CaseRangeProof(d7_r3_s0_ids, d7_r3_s0_units, edge, 0, 306)

private theorem d7_r3_s0_sem_306_613 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 306, 613) := by
  exact d12CaseRangeProof(d7_r3_s0_ids, d7_r3_s0_units, edge, 306, 613)

private theorem d7_r3_s0_sem_0_613 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 0, 613) := by
  intro h
  exact h.elim (d7_r3_s0_sem_0_306 edge) (d7_r3_s0_sem_306_613 edge)

private theorem d7_r3_s0_sem_613_919 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 613, 919) := by
  exact d12CaseRangeProof(d7_r3_s0_ids, d7_r3_s0_units, edge, 613, 919)

private theorem d7_r3_s0_sem_919_1226 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 919, 1226) := by
  exact d12CaseRangeProof(d7_r3_s0_ids, d7_r3_s0_units, edge, 919, 1226)

private theorem d7_r3_s0_sem_613_1226 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 613, 1226) := by
  intro h
  exact h.elim (d7_r3_s0_sem_613_919 edge) (d7_r3_s0_sem_919_1226 edge)

private theorem d7_r3_s0_sem_0_1226 (edge : Nat → Prop) :
    d12CaseRange(d7_r3_s0_ids, d7_r3_s0_units, edge, 0, 1226) := by
  intro h
  exact h.elim (d7_r3_s0_sem_0_613 edge) (d7_r3_s0_sem_613_1226 edge)

theorem d7_r3_s0 (edge : Nat → Prop) : D12Outcome edge d7_r3_s0_units := by
  exact d7_r3_s0_sem_0_1226 edge (d12CaseRaw(d7_r3_s0_raw, edge))

end Erdos758.D12Certificate
