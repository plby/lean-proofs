import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s2_raw
  (include_str "../reduced/d7_r2_s2.cnf")
  (include_str "../reduced/d7_r2_s2.lrat")

def d7_r2_s2_ids : String := include_str "../reduced/d7_r2_s2.ids"

def d7_r2_s2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, true), (20, false), (21, false)]

private theorem d7_r2_s2_sem_0_389 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 0, 389) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 0, 389)

private theorem d7_r2_s2_sem_389_779 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 389, 779) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 389, 779)

private theorem d7_r2_s2_sem_0_779 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 0, 779) := by
  intro h
  exact h.elim (d7_r2_s2_sem_0_389 edge) (d7_r2_s2_sem_389_779 edge)

private theorem d7_r2_s2_sem_779_1169 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 779, 1169) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 779, 1169)

private theorem d7_r2_s2_sem_1169_1559 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 1169, 1559) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 1169, 1559)

private theorem d7_r2_s2_sem_779_1559 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 779, 1559) := by
  intro h
  exact h.elim (d7_r2_s2_sem_779_1169 edge) (d7_r2_s2_sem_1169_1559 edge)

private theorem d7_r2_s2_sem_0_1559 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 0, 1559) := by
  intro h
  exact h.elim (d7_r2_s2_sem_0_779 edge) (d7_r2_s2_sem_779_1559 edge)

private theorem d7_r2_s2_sem_1559_1948 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 1559, 1948) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 1559, 1948)

private theorem d7_r2_s2_sem_1948_2338 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 1948, 2338) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 1948, 2338)

private theorem d7_r2_s2_sem_1559_2338 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 1559, 2338) := by
  intro h
  exact h.elim (d7_r2_s2_sem_1559_1948 edge) (d7_r2_s2_sem_1948_2338 edge)

private theorem d7_r2_s2_sem_2338_2728 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 2338, 2728) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 2338, 2728)

private theorem d7_r2_s2_sem_2728_3118 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 2728, 3118) := by
  exact d12CaseRangeProof(d7_r2_s2_ids, d7_r2_s2_units, edge, 2728, 3118)

private theorem d7_r2_s2_sem_2338_3118 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 2338, 3118) := by
  intro h
  exact h.elim (d7_r2_s2_sem_2338_2728 edge) (d7_r2_s2_sem_2728_3118 edge)

private theorem d7_r2_s2_sem_1559_3118 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 1559, 3118) := by
  intro h
  exact h.elim (d7_r2_s2_sem_1559_2338 edge) (d7_r2_s2_sem_2338_3118 edge)

private theorem d7_r2_s2_sem_0_3118 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s2_ids, d7_r2_s2_units, edge, 0, 3118) := by
  intro h
  exact h.elim (d7_r2_s2_sem_0_1559 edge) (d7_r2_s2_sem_1559_3118 edge)

theorem d7_r2_s2 (edge : Nat → Prop) : D12Outcome edge d7_r2_s2_units := by
  exact d7_r2_s2_sem_0_3118 edge (d12CaseRaw(d7_r2_s2_raw, edge))

end Erdos758.D12Certificate
