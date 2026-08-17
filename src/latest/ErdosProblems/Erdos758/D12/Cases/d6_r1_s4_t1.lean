import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s4_t1_raw
  (include_str "../reduced/d6_r1_s4_t1.cnf")
  (include_str "../reduced/d6_r1_s4_t1.lrat")

def d6_r1_s4_t1_ids : String := include_str "../reduced/d6_r1_s4_t1.ids"

def d6_r1_s4_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (22, true), (23, false), (24, false), (25, false)]

private theorem d6_r1_s4_t1_sem_0_282 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 0, 282) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 0, 282)

private theorem d6_r1_s4_t1_sem_282_564 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 282, 564) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 282, 564)

private theorem d6_r1_s4_t1_sem_0_564 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 0, 564) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_0_282 edge) (d6_r1_s4_t1_sem_282_564 edge)

private theorem d6_r1_s4_t1_sem_564_846 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 564, 846) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 564, 846)

private theorem d6_r1_s4_t1_sem_846_1129 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 846, 1129) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 846, 1129)

private theorem d6_r1_s4_t1_sem_564_1129 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 564, 1129) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_564_846 edge) (d6_r1_s4_t1_sem_846_1129 edge)

private theorem d6_r1_s4_t1_sem_0_1129 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 0, 1129) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_0_564 edge) (d6_r1_s4_t1_sem_564_1129 edge)

private theorem d6_r1_s4_t1_sem_1129_1411 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1129, 1411) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1129, 1411)

private theorem d6_r1_s4_t1_sem_1411_1693 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1411, 1693) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1411, 1693)

private theorem d6_r1_s4_t1_sem_1129_1693 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1129, 1693) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_1129_1411 edge) (d6_r1_s4_t1_sem_1411_1693 edge)

private theorem d6_r1_s4_t1_sem_1693_1975 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1693, 1975) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1693, 1975)

private theorem d6_r1_s4_t1_sem_1975_2258 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1975, 2258) := by
  exact d12CaseRangeProof(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1975, 2258)

private theorem d6_r1_s4_t1_sem_1693_2258 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1693, 2258) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_1693_1975 edge) (d6_r1_s4_t1_sem_1975_2258 edge)

private theorem d6_r1_s4_t1_sem_1129_2258 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 1129, 2258) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_1129_1693 edge) (d6_r1_s4_t1_sem_1693_2258 edge)

private theorem d6_r1_s4_t1_sem_0_2258 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s4_t1_ids, d6_r1_s4_t1_units, edge, 0, 2258) := by
  intro h
  exact h.elim (d6_r1_s4_t1_sem_0_1129 edge) (d6_r1_s4_t1_sem_1129_2258 edge)

theorem d6_r1_s4_t1 (edge : Nat → Prop) : D12Outcome edge d6_r1_s4_t1_units := by
  exact d6_r1_s4_t1_sem_0_2258 edge (d12CaseRaw(d6_r1_s4_t1_raw, edge))

end Erdos758.D12Certificate
