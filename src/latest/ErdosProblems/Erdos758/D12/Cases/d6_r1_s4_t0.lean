import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s4_t0_raw
  (include_str "../reduced/d6_r1_s4_t0.cnf")
  (include_str "../reduced/d6_r1_s4_t0.lrat")

def d6_r1_s4_t0_ids : String := include_str "../reduced/d6_r1_s4_t0.ids"

def d6_r1_s4_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (22, false), (23, false), (24, false), (25, false)]

private theorem d6_r1_s4_t0_sem_0_268 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 0, 268) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 0, 268)

private theorem d6_r1_s4_t0_sem_268_536 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 268, 536) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 268, 536)

private theorem d6_r1_s4_t0_sem_0_536 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 0, 536) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_0_268 edge) (d6_r1_s4_t0_sem_268_536 edge)

private theorem d6_r1_s4_t0_sem_536_804 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 536, 804) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 536, 804)

private theorem d6_r1_s4_t0_sem_804_1072 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 804, 1072) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 804, 1072)

private theorem d6_r1_s4_t0_sem_536_1072 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 536, 1072) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_536_804 edge) (d6_r1_s4_t0_sem_804_1072 edge)

private theorem d6_r1_s4_t0_sem_0_1072 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 0, 1072) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_0_536 edge) (d6_r1_s4_t0_sem_536_1072 edge)

private theorem d6_r1_s4_t0_sem_1072_1340 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1072, 1340) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1072, 1340)

private theorem d6_r1_s4_t0_sem_1340_1608 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1340, 1608) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1340, 1608)

private theorem d6_r1_s4_t0_sem_1072_1608 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1072, 1608) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_1072_1340 edge) (d6_r1_s4_t0_sem_1340_1608 edge)

private theorem d6_r1_s4_t0_sem_1608_1876 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1608, 1876) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1608, 1876)

private theorem d6_r1_s4_t0_sem_1876_2145 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1876, 2145) := by
  exact d12CaseRangeProof(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1876, 2145)

private theorem d6_r1_s4_t0_sem_1608_2145 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1608, 2145) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_1608_1876 edge) (d6_r1_s4_t0_sem_1876_2145 edge)

private theorem d6_r1_s4_t0_sem_1072_2145 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 1072, 2145) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_1072_1608 edge) (d6_r1_s4_t0_sem_1608_2145 edge)

private theorem d6_r1_s4_t0_sem_0_2145 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t0_ids, d6_r1_s4_t0_units, edge, 0, 2145) := by
  intro h
  exact h.elim (d6_r1_s4_t0_sem_0_1072 edge) (d6_r1_s4_t0_sem_1072_2145 edge)

theorem d6_r1_s4_t0 (edge : Nat → Prop) : D12Outcome edge d6_r1_s4_t0_units := by
  exact d6_r1_s4_t0_sem_0_2145 edge (d12CaseRaw(d6_r1_s4_t0_raw, edge))

end Erdos758.D12Certificate
