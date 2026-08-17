import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s0_raw
  (include_str "../reduced/d6_r1_s0.cnf")
  (include_str "../reduced/d6_r1_s0.lrat")

def d6_r1_s0_ids : String := include_str "../reduced/d6_r1_s0.ids"

def d6_r1_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r1_s0_sem_0_365 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 0, 365) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 0, 365)

private theorem d6_r1_s0_sem_365_731 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 365, 731) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 365, 731)

private theorem d6_r1_s0_sem_0_731 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 0, 731) := by
  intro h
  exact h.elim (d6_r1_s0_sem_0_365 edge) (d6_r1_s0_sem_365_731 edge)

private theorem d6_r1_s0_sem_731_1096 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 731, 1096) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 731, 1096)

private theorem d6_r1_s0_sem_1096_1462 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 1096, 1462) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 1096, 1462)

private theorem d6_r1_s0_sem_731_1462 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 731, 1462) := by
  intro h
  exact h.elim (d6_r1_s0_sem_731_1096 edge) (d6_r1_s0_sem_1096_1462 edge)

private theorem d6_r1_s0_sem_0_1462 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 0, 1462) := by
  intro h
  exact h.elim (d6_r1_s0_sem_0_731 edge) (d6_r1_s0_sem_731_1462 edge)

private theorem d6_r1_s0_sem_1462_1827 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 1462, 1827) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 1462, 1827)

private theorem d6_r1_s0_sem_1827_2193 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 1827, 2193) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 1827, 2193)

private theorem d6_r1_s0_sem_1462_2193 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 1462, 2193) := by
  intro h
  exact h.elim (d6_r1_s0_sem_1462_1827 edge) (d6_r1_s0_sem_1827_2193 edge)

private theorem d6_r1_s0_sem_2193_2559 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 2193, 2559) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 2193, 2559)

private theorem d6_r1_s0_sem_2559_2925 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 2559, 2925) := by
  exact d12CaseRangeProof(d6_r1_s0_ids, d6_r1_s0_units, edge, 2559, 2925)

private theorem d6_r1_s0_sem_2193_2925 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 2193, 2925) := by
  intro h
  exact h.elim (d6_r1_s0_sem_2193_2559 edge) (d6_r1_s0_sem_2559_2925 edge)

private theorem d6_r1_s0_sem_1462_2925 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 1462, 2925) := by
  intro h
  exact h.elim (d6_r1_s0_sem_1462_2193 edge) (d6_r1_s0_sem_2193_2925 edge)

private theorem d6_r1_s0_sem_0_2925 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s0_ids, d6_r1_s0_units, edge, 0, 2925) := by
  intro h
  exact h.elim (d6_r1_s0_sem_0_1462 edge) (d6_r1_s0_sem_1462_2925 edge)

theorem d6_r1_s0 (edge : Nat → Prop) : D12Outcome edge d6_r1_s0_units := by
  exact d6_r1_s0_sem_0_2925 edge (d12CaseRaw(d6_r1_s0_raw, edge))

end Erdos758.D12Certificate
