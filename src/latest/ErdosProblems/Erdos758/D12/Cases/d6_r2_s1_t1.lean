import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s1_t1_raw
  (include_str "../reduced/d6_r2_s1_t1.cnf")
  (include_str "../reduced/d6_r2_s1_t1.lrat")

def d6_r2_s1_t1_ids : String := include_str "../reduced/d6_r2_s1_t1.ids"

def d6_r2_s1_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (23, true), (24, false), (25, false)]

private theorem d6_r2_s1_t1_sem_0_333 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 0, 333) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 0, 333)

private theorem d6_r2_s1_t1_sem_333_666 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 333, 666) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 333, 666)

private theorem d6_r2_s1_t1_sem_0_666 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 0, 666) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_0_333 edge) (d6_r2_s1_t1_sem_333_666 edge)

private theorem d6_r2_s1_t1_sem_666_999 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 666, 999) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 666, 999)

private theorem d6_r2_s1_t1_sem_999_1332 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 999, 1332) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 999, 1332)

private theorem d6_r2_s1_t1_sem_666_1332 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 666, 1332) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_666_999 edge) (d6_r2_s1_t1_sem_999_1332 edge)

private theorem d6_r2_s1_t1_sem_0_1332 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 0, 1332) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_0_666 edge) (d6_r2_s1_t1_sem_666_1332 edge)

private theorem d6_r2_s1_t1_sem_1332_1665 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1332, 1665) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1332, 1665)

private theorem d6_r2_s1_t1_sem_1665_1998 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1665, 1998) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1665, 1998)

private theorem d6_r2_s1_t1_sem_1332_1998 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1332, 1998) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_1332_1665 edge) (d6_r2_s1_t1_sem_1665_1998 edge)

private theorem d6_r2_s1_t1_sem_1998_2331 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1998, 2331) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1998, 2331)

private theorem d6_r2_s1_t1_sem_2331_2665 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 2331, 2665) := by
  exact d12CaseRangeProof(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 2331, 2665)

private theorem d6_r2_s1_t1_sem_1998_2665 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1998, 2665) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_1998_2331 edge) (d6_r2_s1_t1_sem_2331_2665 edge)

private theorem d6_r2_s1_t1_sem_1332_2665 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 1332, 2665) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_1332_1998 edge) (d6_r2_s1_t1_sem_1998_2665 edge)

private theorem d6_r2_s1_t1_sem_0_2665 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t1_ids, d6_r2_s1_t1_units, edge, 0, 2665) := by
  intro h
  exact h.elim (d6_r2_s1_t1_sem_0_1332 edge) (d6_r2_s1_t1_sem_1332_2665 edge)

theorem d6_r2_s1_t1 (edge : Nat → Prop) : D12Outcome edge d6_r2_s1_t1_units := by
  exact d6_r2_s1_t1_sem_0_2665 edge (d12CaseRaw(d6_r2_s1_t1_raw, edge))

end Erdos758.D12Certificate
