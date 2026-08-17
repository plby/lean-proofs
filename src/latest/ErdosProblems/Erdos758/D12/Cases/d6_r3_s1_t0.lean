import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s1_t0_raw
  (include_str "../reduced/d6_r3_s1_t0.cnf")
  (include_str "../reduced/d6_r3_s1_t0.lrat")

def d6_r3_s1_t0_ids : String := include_str "../reduced/d6_r3_s1_t0.ids"

def d6_r3_s1_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (24, false), (25, false)]

private theorem d6_r3_s1_t0_sem_0_256 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 0, 256) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 0, 256)

private theorem d6_r3_s1_t0_sem_256_513 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 256, 513) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 256, 513)

private theorem d6_r3_s1_t0_sem_0_513 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 0, 513) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_0_256 edge) (d6_r3_s1_t0_sem_256_513 edge)

private theorem d6_r3_s1_t0_sem_513_769 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 513, 769) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 513, 769)

private theorem d6_r3_s1_t0_sem_769_1026 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 769, 1026) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 769, 1026)

private theorem d6_r3_s1_t0_sem_513_1026 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 513, 1026) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_513_769 edge) (d6_r3_s1_t0_sem_769_1026 edge)

private theorem d6_r3_s1_t0_sem_0_1026 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 0, 1026) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_0_513 edge) (d6_r3_s1_t0_sem_513_1026 edge)

private theorem d6_r3_s1_t0_sem_1026_1282 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1026, 1282) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1026, 1282)

private theorem d6_r3_s1_t0_sem_1282_1539 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1282, 1539) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1282, 1539)

private theorem d6_r3_s1_t0_sem_1026_1539 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1026, 1539) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_1026_1282 edge) (d6_r3_s1_t0_sem_1282_1539 edge)

private theorem d6_r3_s1_t0_sem_1539_1795 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1539, 1795) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1539, 1795)

private theorem d6_r3_s1_t0_sem_1795_2052 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1795, 2052) := by
  exact d12CaseRangeProof(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1795, 2052)

private theorem d6_r3_s1_t0_sem_1539_2052 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1539, 2052) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_1539_1795 edge) (d6_r3_s1_t0_sem_1795_2052 edge)

private theorem d6_r3_s1_t0_sem_1026_2052 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 1026, 2052) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_1026_1539 edge) (d6_r3_s1_t0_sem_1539_2052 edge)

private theorem d6_r3_s1_t0_sem_0_2052 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t0_ids, d6_r3_s1_t0_units, edge, 0, 2052) := by
  intro h
  exact h.elim (d6_r3_s1_t0_sem_0_1026 edge) (d6_r3_s1_t0_sem_1026_2052 edge)

theorem d6_r3_s1_t0 (edge : Nat → Prop) : D12Outcome edge d6_r3_s1_t0_units := by
  exact d6_r3_s1_t0_sem_0_2052 edge (d12CaseRaw(d6_r3_s1_t0_raw, edge))

end Erdos758.D12Certificate
