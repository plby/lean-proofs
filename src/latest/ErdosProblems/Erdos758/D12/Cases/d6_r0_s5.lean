import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s5_raw
  (include_str "../reduced/d6_r0_s5.cnf")
  (include_str "../reduced/d6_r0_s5.lrat")

def d6_r0_s5_ids : String := include_str "../reduced/d6_r0_s5.ids"

def d6_r0_s5_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, true)]

private theorem d6_r0_s5_sem_0_289 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 0, 289) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 0, 289)

private theorem d6_r0_s5_sem_289_578 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 289, 578) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 289, 578)

private theorem d6_r0_s5_sem_0_578 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 0, 578) := by
  intro h
  exact h.elim (d6_r0_s5_sem_0_289 edge) (d6_r0_s5_sem_289_578 edge)

private theorem d6_r0_s5_sem_578_867 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 578, 867) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 578, 867)

private theorem d6_r0_s5_sem_867_1156 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 867, 1156) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 867, 1156)

private theorem d6_r0_s5_sem_578_1156 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 578, 1156) := by
  intro h
  exact h.elim (d6_r0_s5_sem_578_867 edge) (d6_r0_s5_sem_867_1156 edge)

private theorem d6_r0_s5_sem_0_1156 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 0, 1156) := by
  intro h
  exact h.elim (d6_r0_s5_sem_0_578 edge) (d6_r0_s5_sem_578_1156 edge)

private theorem d6_r0_s5_sem_1156_1445 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1156, 1445) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 1156, 1445)

private theorem d6_r0_s5_sem_1445_1734 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1445, 1734) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 1445, 1734)

private theorem d6_r0_s5_sem_1156_1734 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1156, 1734) := by
  intro h
  exact h.elim (d6_r0_s5_sem_1156_1445 edge) (d6_r0_s5_sem_1445_1734 edge)

private theorem d6_r0_s5_sem_1734_2023 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1734, 2023) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 1734, 2023)

private theorem d6_r0_s5_sem_2023_2313 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 2023, 2313) := by
  exact d12CaseRangeProof(d6_r0_s5_ids, d6_r0_s5_units, edge, 2023, 2313)

private theorem d6_r0_s5_sem_1734_2313 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1734, 2313) := by
  intro h
  exact h.elim (d6_r0_s5_sem_1734_2023 edge) (d6_r0_s5_sem_2023_2313 edge)

private theorem d6_r0_s5_sem_1156_2313 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 1156, 2313) := by
  intro h
  exact h.elim (d6_r0_s5_sem_1156_1734 edge) (d6_r0_s5_sem_1734_2313 edge)

private theorem d6_r0_s5_sem_0_2313 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s5_ids, d6_r0_s5_units, edge, 0, 2313) := by
  intro h
  exact h.elim (d6_r0_s5_sem_0_1156 edge) (d6_r0_s5_sem_1156_2313 edge)

theorem d6_r0_s5 (edge : Nat → Prop) : D12Outcome edge d6_r0_s5_units := by
  exact d6_r0_s5_sem_0_2313 edge (d12CaseRaw(d6_r0_s5_raw, edge))

end Erdos758.D12Certificate
