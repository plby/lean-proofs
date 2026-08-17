import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s5_raw
  (include_str "../reduced/d6_r2_s5.cnf")
  (include_str "../reduced/d6_r2_s5.lrat")

def d6_r2_s5_ids : String := include_str "../reduced/d6_r2_s5.ids"

def d6_r2_s5_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, true)]

private theorem d6_r2_s5_sem_0_365 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 0, 365) := by
  exact d12CaseRangeProof(d6_r2_s5_ids, d6_r2_s5_units, edge, 0, 365)

private theorem d6_r2_s5_sem_365_730 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 365, 730) := by
  exact d12CaseRangeProof(d6_r2_s5_ids, d6_r2_s5_units, edge, 365, 730)

private theorem d6_r2_s5_sem_0_730 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 0, 730) := by
  intro h
  exact h.elim (d6_r2_s5_sem_0_365 edge) (d6_r2_s5_sem_365_730 edge)

private theorem d6_r2_s5_sem_730_1095 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 730, 1095) := by
  exact d12CaseRangeProof(d6_r2_s5_ids, d6_r2_s5_units, edge, 730, 1095)

private theorem d6_r2_s5_sem_1095_1461 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 1095, 1461) := by
  exact d12CaseRangeProof(d6_r2_s5_ids, d6_r2_s5_units, edge, 1095, 1461)

private theorem d6_r2_s5_sem_730_1461 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 730, 1461) := by
  intro h
  exact h.elim (d6_r2_s5_sem_730_1095 edge) (d6_r2_s5_sem_1095_1461 edge)

private theorem d6_r2_s5_sem_0_1461 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s5_ids, d6_r2_s5_units, edge, 0, 1461) := by
  intro h
  exact h.elim (d6_r2_s5_sem_0_730 edge) (d6_r2_s5_sem_730_1461 edge)

theorem d6_r2_s5 (edge : Nat → Prop) : D12Outcome edge d6_r2_s5_units := by
  exact d6_r2_s5_sem_0_1461 edge (d12CaseRaw(d6_r2_s5_raw, edge))

end Erdos758.D12Certificate
